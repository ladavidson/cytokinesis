//		Micro vertex model for cytokinetic furrow analysis; March 25, 2024 Lance Davidson, lad43@pitt.edu
//	
// This macro simulates progression of a cytokinetic furrow during the final phase of 
// cell division. The simulation is based on vertex model described in Weliky and Oster (1990) but 
// with mechanically heterogeneous cell mechanics and modifications for furrow formation.
//
// Basic cell mechanics includes bicellular junctions (BCJ) whose physical properties are a blend
// of the two cells' mechanical properties. BCJs are subject to pressure and tensional forces: 
//		i) spring forces due to tensional elasticity of the apical junctional complex, 
//		ii) volumetric contraint on each cell, mimicking bulk elasticity of the cell interior, 
//			here the medioapical cortex.
//		iii) if the cell is on the edge, it it attached to a tether connecting each vertex to the boundary.
//
// As per conventional vertex models, forces act to displace tricellular junctions or vertices.
//
// Here we simulate the mechanical events following creation of a furrow in a dividing cell. 
// We add a fourth force acting on a novel junction type, the nascent cellular junction or furrow vertex. 
// The furrow vertex is present where the dividing cell builds a new junction at a point on the BCJ shared with
// neighboring cells. Furrow vertices anchor the cytokinetic furrow to neighboring cells. 
//
// Initially, all cells will be identical with positions of the furrow vertices along the BCJ of 
//		the two opposing neighbor cells.
//
// The initial code is structured to prepare for parameter sweeps and variation of:
// a) 6 biophysical properties of the central seven cells and one fake border cell including:
//		cell-perimeter rest length and perimeter or junction spring-string stiffness, 
//		area rest length and volume/area stiffness.
//		tether rest length and stiffness
// b) Biomechanical properties of the surrounding tissue are mimicked by attaching neighbor cells to an
// 		circular boundary domain by tethers and area of fake border cell.
// c) Furrowing force (a dipole force) at each of the opposing furrow vertices.
// d) Two cell mechanical experiments are implemented in the vertex code. These represent mosaic expression of 
//			factors such as anillin that increase F-actin density, e.g. stiffness, and optogenetic regulation
//			of RhoA that will drive reduction in the cell area and perimeter. The two perturbations are similar
//			but not exactly the same in the way they modulate tissue mechanics.
//		i) Enhancing cell stiffness in a subset of cells (e.g. through overexpression).
//		ii) Enhancing cell contractility, but reducing the rest area or rest perimeter in a subset of cells
//			(e.g. through optogenetic stimulation).
//
// Model time advances in stepwise form, with each vertex moving according to vector sum of
// applied forces and global viscosity.
//
//	Cell geometries remodel in response to applied forces.
//
// 1. Initialize the geometry of the central cell, 6 surrounding cells, and bounding tissue attachments.
// 2. Advance the simulation until the network reaches positional stability.
// 3. (Optional) Expand the area of the central cell.
// 4. Add tension at apposed furrow vertex points.
// 5. Advance the simulation.
// 6. (Optional) Include mechanical perturbation.
// 7. Output timelapse with model parameters (time-stamped avi file).
// 8. Output log file with cell areas (A) and perimeters (P), positional data on furrow width (F), distances
//		of each furrow vertex point to fixed point on the periphery (Ftop and Fbot), and the approximate force generated 
//		generated from area (pressure) and perimeter springs (tension) in each cell.
//
// (Optional) BATCH mode. Run repetitions of the simulation with the same parameter settings. Random fluctuations in position 
//		simulate biological replicates. In this mode only furrow width (F) and distances to fixed points on the 
//		periphery (Ftop and Fbot), are saved in a time-stamped text file.
//
//
//	240611 - Make the springs linear with length/area, not scaled for strain/area_strain.
//
//  ------------------------------------------------------------------------------------------------------------------------
//  ------------------------------------------------------------------------------------------------------------------------
//

var runTypes = newArray("Hex ROI Set", "Sorry - Only Runs Hex Set");
var runType;
var totT = 400;
var furrowT = 100;
var furrowOFF = 401;
var nu = 1.0;
var dT = 0.2;

var furrowF = 0.015;
var kspringT = 1;
var kspringJ = 0.5;
var kspringA = 0.5;

var restAFactor = 0.9;
var restJFactor = 0.9;

var grow = false;
var growT = 401;
var areafactor = 1.5;  // increase area of dividing cell by this factor -- before cytokinesis starts

var stiff = true;
var stiffTypes = newArray("cell below", "cell to right", "three cells below", "all cells", "furrowing cell");
var stiffType = "cell below";
var stiffJfactor = 15.;
var stiffAfactor = 4.;

var stifftimeOn = 200;
var stifftimeOff = 300;

var contract = true;
var contractTypes = newArray("cell below", "cell to right", "three cells below", "all cells", "furrowing cell");
var contractType = "cell below";
var contractAfactor = 0.3;
var contractJfactor = 0.5;

var contracttimeOn = 200;
var contracttimeOff = 300;

var showTether = false;
var showPressure = false;
var showJunction = false;

var	runReps = false;
var	nReps = 10;

//
// geometry
//

var wid, hei, nV, nCells;
var xV, yV, typeV;
var vFX, vFY, vDX, vDY;

var cell;
var cell1, cell2, cell3, cell4, cell5, cell6, cell7;
var fakeinner, fakeouter;

var ncell1, ncell2, ncell3, ncell4, ncell5, ncell6, ncell7, ncell8;

var cellarea, cellareai, cellperi, cellperii;
var area1, area2, area3, area4, area5, area6, area7, area8;
var area1i, area2i, area3i, area4i, area5i, area6i, area7i, area8i;

var initarea1, initarea2, initarea3, initarea4, initarea5, initarea6, initarea7, initarea8;

var peri1, peri2, peri3, peri4, peri5, peri6, peri7, peri8;
var peri1i, peri2i, peri3i, peri4i, peri5i, peri6i, peri7i, peri8i;

var initperi1, initperi2, initperi3, initperi4, initperi5, initperi6, initperi7, initperi8;

var star1 = star2 = star2 = star3 = star4 = star5 = star6 = star7 = false;

var tethers, tetherlen, tetherleni;

var linewid;

//
// parameters
//

var wid = 850;
var hei = 850;
var nV = 44;
var nCells = 8;
var nTethers = 18;

var dFdT; // rate of change in the length of the furrow

//
// model references
//

var myCytoBox;
var isFirst;
var showSim = true;
var localdir = "";
var sep;

//
//  ------------------------------------------------------------------------------------------------------------------------
//  ------------------------------------------------------------------------------------------------------------------------
//
//		MAIN
//
//  ------------------------------------------------------------------------------------------------------------------------
//  ------------------------------------------------------------------------------------------------------------------------
//

macro "RunCytokinesis[1]"
{
	if (localdir == "") localdir = getDir("Choose a Directory");
	sep = "/";
	if (getInfo("os.name") != "Windows") sep = "\\";
	
	VertexDialog();
	
	if (runReps) 
	{
		showSim = false;
		for (ijk=1; ijk<=nReps; ijk++)
		{
			runFurrowSim(ijk);
		}
	} else
	{
		runFurrowSim(1);
	}
	
	prefix = outputPrefix();

	if (showSim)
	{
		selectWindow(myCytoBox);
		run("AVI... ", "compression=JPEG frame=30 save=["+localdir+prefix+".avi]");

		selectWindow("Log");
		saveAs("Text", localdir+prefix);
	}
	if (!showSim)
	{
		selectWindow(myCytoBox); close();
		selectWindow("Log");
		saveAs("Text", localdir+prefix);
		run("Close" );
	}
}

macro "InstallUpdatedMacro[2]"
{
	if (localdir == "") localdir = getDir("Choose a Directory");
	sep = "/";
	if (getInfo("os.name") != "Windows") sep = "\\";
	mymacro = localdir+sep+"240611 micro vertex model.ijm";
	run("Install...", "install=["+mymacro+"]");
}

macro "Make KymoGraph[3]"
{
	run("Reslice [/]...", "output=1.000 slice_count=50");
	run("Z Project...", "projection=[Max Intensity]");
	run("Flip Horizontally");
	run("Rotate 90 Degrees Left");
}


//
//  ------------------------------------------------------------------------------------------------------------------------
//  ------------------------------------------------------------------------------------------------------------------------
//
//		MAIN FUNCTIONS
//
//  ------------------------------------------------------------------------------------------------------------------------
//  ------------------------------------------------------------------------------------------------------------------------
//

function runFurrowSim(ijk)
{
	loadGeometry();
	setBatchMode(true);
		
	kspringJ = kspringJ/(1000);
	kspringA = kspringA/(1000*1000);
	kspringT = kspringT/(1000);
    	
//
//	furrow vertices
//
	fstart = 2-1;
	fend = 6-1;
	
//
//	fixed vertices on the tissue boundary
//
	ftop = 27-1;
	fbot = 36-1;
	
	lengthF = sqrt(pow((xV[fstart]-xV[fend]),2) + pow((yV[fstart]-yV[fend]),2));
	
	//
	// Spring constants are estimated based on the geometry of the dividing cell, neighbors, and surrounding tissues.
	//
	
	var bigstringA = "";
	var bigstringP = "";
	var bigstringF = "";
	var bigstringPressure = "";
	var bigstringTension = "";
	
	//
	// Prior to cytokinesis furrow points move as any other point, no extra force on the furrow.
	//
	
	dFdT = 0;
	
	printParameters();
			
	kJ1 = kJ2 = kJ3 = kJ4 = kJ5 = kJ6 = kJ7 = kJ8 = kspringJ;
	kA1 = kA2 = kA3 = kA4 = kA5 = kA6 = kA7 = kA8 = kspringA;
	
	for (j=1; j<=totT; j++) 
	{
		if (grow && j == growT)
		{
			area1i = areafactor*area1i; // change area of dividing cell
			peri1i = sqrt(areafactor)*peri1i; // change perimeter to match double area
		}
		
//
//
// VARYING STIFFNESS --- assign different stiffness to junctions and area springs.
//
//
		
		if (stiff == true && j == stifftimeOn)
		{
			tstring = "At time: "+j+" Turn ON Stiffness...";
			if (stiffType == "cell below")
			{
				tstring = tstring + " in cell below";
				kJ5 = stiffJfactor*kspringJ;
				kA5 = stiffAfactor*kspringA;
				star5 = true;
			}
			else if (stiffType == "cell to right")
			{
				tstring = tstring + " in cell to right";
				kJ4 = stiffJfactor*kspringJ;
				kA4 = stiffAfactor*kspringA;
				star4 = true;
			}
			else if (stiffType == "three cells below")
			{
				tstring = tstring + " in three cells below";
				kJ4 = stiffJfactor*kspringJ;
				kA4 = stiffAfactor*kspringA;
				star4 = true;
				
				kJ5 = stiffJfactor*kspringJ;
				kA5 = stiffAfactor*kspringA;
				star5 = true;
				
				kJ6 = stiffJfactor*kspringJ;
				kA6 = stiffAfactor*kspringA;
				star6 = true;
			}
			else if (stiffType == "all cells")
			{
				tstring = tstring + " in all cells";
				kJ1 = stiffJfactor*kspringJ;
				kA1 = stiffAfactor*kspringA;
				star1 = true;				
				
				kJ2 = stiffJfactor*kspringJ;
				kA2 = stiffAfactor*kspringA;
				star2 = true;				
				
				kJ3 = stiffJfactor*kspringJ;
				kA3 = stiffAfactor*kspringA;
				star3 = true;
				
				kJ4 = stiffJfactor*kspringJ;
				kA4 = stiffAfactor*kspringA;
				star4 = true;
				
				kJ5 = stiffJfactor*kspringJ;
				kA5 = stiffAfactor*kspringA;
				star5 = true;
				
				kJ6 = stiffJfactor*kspringJ;
				kA6 = stiffAfactor*kspringA;
				star6 = true;

				kJ7 = stiffJfactor*kspringJ;
				kA7 = stiffAfactor*kspringA;
				star7 = true;
			}
			else if (stiffType == "furrowing cell")
			{
				tstring = tstring + " in furrowing cell";
				kJ1 = stiffJfactor*kspringJ;
				kA1 = stiffAfactor*kspringA;
				star1 = true;
			}
//			print(tstring); tstring = "";
		}
		
		if (stiff == true && j == stifftimeOff)
		{
//			print ("At time: "+j+" Turn OFF Stiffening... reset ALL");
			kJ1 = kJ2 = kJ3 = kJ4 = kJ5 = kJ6 = kJ7 = kJ8 = kspringJ;
			kA1 = kA2 = kA3 = kA4 = kA5 = kA6 = kA7 = kA8 = kspringA;
			
			star1 = star2 = star3 = star4 = star5 = star6 = star7 = false;
		}
		
//
//
//  VARYING CONTRACTILTY - reduce the rest area and junction lengths.
//
//
		
		if (contract == true && j == contracttimeOn)
		{
			tstring = "At time: "+j+" Turn ON Opto Contraction...";
//			print("BEFORE: peri to initial: "+peri1i+", "+peri2i+", "+peri3i+", "+peri4i+", "+peri5i+", "+peri6i+", "+peri7i);
//			print("BEFORE: area to initial: "+area1i+", "+area2i+", "+area3i+", "+area4i+", "+area5i+", "+area6i+", "+area7i);
			if (contractType == "cell below")
			{
				tstring = tstring + " in cell below";
				peri5i = contractJfactor*initperi5;
				area5i = contractAfactor*initarea5;
				star5 = true;
			}
			else if (contractType == "cell to right")
			{
				tstring = tstring + " in cell to right";
				peri4i = contractJfactor*initperi4;
				area4i = contractAfactor*initarea4;
				star4 = true;
			}
			else if (contractType == "three cells below")
			{	
				tstring = tstring + " in three cells below";
				peri4i = contractJfactor*initperi4;
				area4i = contractAfactor*initarea4;
				star4 = true;

				peri5i = contractJfactor*initperi5;
				area5i = contractAfactor*initarea5;
				star5 = true;
		
				peri6i = contractJfactor*initperi6;
				area6i = contractAfactor*initarea6;	
				star6 = true;
			}
			else if (contractType == "all cells")
			{
				tstring = tstring + " in all cells";
				peri1i = contractJfactor*initperi1;
				area1i = contractAfactor*initarea1;
				star1 = true;
							
				peri2i = contractJfactor*initperi2;
				area2i = contractAfactor*initarea2;
				star2 = true;
							
				peri3i = contractJfactor*initperi3;
				area3i = contractAfactor*initarea3;
				star3 = true;
							
				peri4i = contractJfactor*initperi4;
				area4i = contractAfactor*initarea4;
				star4 = true;

				peri5i = contractJfactor*initperi5;
				area5i = contractAfactor*initarea5;
				star5 = true;
		
				peri6i = contractJfactor*initperi6;
				area6i = contractAfactor*initarea6;
				star6 = true;
						
				peri7i = contractJfactor*initperi7;
				area7i = contractAfactor*initarea7;
				star7 = true;
			}
			else if (contractType == "furrowing cell")
			{
				tstring = tstring + " in furrowing cell";
				peri1i = contractJfactor*initperi1;
				area1i = contractAfactor*initarea1;
				star1 = true;
			}
//			print("CONTRACT: peri to initial: "+peri1i+", "+peri2i+", "+peri3i+", "+peri4i+", "+peri5i+", "+peri6i+", "+peri7i);
//			print("CONTRACT: area to initial: "+area1i+", "+area2i+", "+area3i+", "+area4i+", "+area5i+", "+area6i+", "+area7i);
//			print(tstring); tstring = "";
		}
		
		if (contract == true && j == contracttimeOff)  // Reset areas and perimeters
		{
//			print ("At time: "+j+" Turn OFF Opto Contraction... reset ALL");
					
			peri1i = initperi1;
			peri2i = initperi2;
			peri3i = initperi3;
			peri4i = initperi4;
			peri5i = initperi5;
			peri6i = initperi6;
			peri7i = initperi7;
			
			area1i = initarea1;
			area2i = initarea2;
			area3i = initarea3;
			area4i = initarea4;
			area5i = initarea5;
			area6i = initarea6;
			area7i = initarea7;
			
			star1 = star2 = star3 = star4 = star5 = star6 = star7 = false;
			
//			print("RESET: peri to initial: "+peri1i+", "+peri2i+", "+peri3i+", "+peri4i+", "+peri5i+", "+peri6i+", "+peri7i);
//			print("RESET: area to initial: "+area1i+", "+area2i+", "+area3i+", "+area4i+", "+area5i+", "+area6i+", "+area7i);
		}		

		if (showSim)
		{
			drawGeometry();
			drawParameters();
		
			if (showTether) drawTethers(1, 255, 105, 0); // (255, 105, 0) is "orange"
			if (showPressure) drawPressure(-1, fakeinner, ncell8, 0, 255, 255); // "cyan"
			if (showJunction)
			{
				drawJ(cell1, ncell1, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell2, ncell2, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell3, ncell3, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell4, ncell4, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell5, ncell5, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell6, ncell6, 2, 0, 210, 0); // (0, 210, 0) "green"
				drawJ(cell7, ncell7, 2, 0, 210, 0); // (0, 210, 0) "green"
			}
		}		
		zeroForce(vFX, vFY); 
		zeroDisp(vDX, vDY);
		
//
//	Calculate forces at each vertex due to tethers, pressure, and junctions
//			
		calcTetherForce(kspringT, vFX, vFY);
		calcAllCellPressure(kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8);
		calcAllJunctionForce(kJ1, kJ2, kJ3, kJ4, kJ5, kJ6, kJ7, kJ8, vFX, vFY); // 

//
//	Drive cytokinesis -- move the furrow ends
// ********************************************
//
		if (j == furrowT)
		{ 
			dFdT = furrowF;
//			print ("At time: "+j+" Turn ON Furrow Force...");
		}
		if (j == furrowOFF)
		{
			dFdT = 0;	
//			print ("At time: "+j+" Turn OFF Furrow Force...");
		}
		
		lengthF = sqrt(pow((xV[fstart]-xV[fend]),2) + pow((yV[fstart]-yV[fend]),2));

		dFXdT = dFdT*(xV[fstart]-xV[fend]);
		dFYdT = dFdT*(yV[fstart]-yV[fend]);
		
//
// ********************************************
//
		
		calcDisp(dT, nu, vFX, vFY, vDX, vDY);

		randmoveVX(25, vDX, vDY);
		
		moveVx(25, vDX, vDY);

		moveFx(dFXdT, dFYdT);
		
//
// Update tether lengths, areas, perimeters, furrow length, and furrow position from top and bottom external points.
// Format and write output.
//
		
		calcTetherLength();
		
		area1 = calcArea(cell1, xV, yV, ncell1);
		area2 = calcArea(cell2, xV, yV, ncell2);
		area3 = calcArea(cell3, xV, yV, ncell3);
		area4 = calcArea(cell4, xV, yV, ncell4);
		area5 = calcArea(cell5, xV, yV, ncell5);
		area6 = calcArea(cell6, xV, yV, ncell6);
		area7 = calcArea(cell7, xV, yV, ncell7);
		area8 = calcArea(fakeouter, xV, yV, ncell8) - calcArea(fakeinner, xV, yV, ncell8);
		
		peri1 = calcPeri(cell1, xV, yV, ncell1);
		peri2 = calcPeri(cell2, xV, yV, ncell2);
		peri3 = calcPeri(cell3, xV, yV, ncell3);	
		peri4 = calcPeri(cell4, xV, yV, ncell4);
		peri5 = calcPeri(cell5, xV, yV, ncell5);
		peri6 = calcPeri(cell6, xV, yV, ncell6);
		peri7 = calcPeri(cell7, xV, yV, ncell7);
		peri8 = calcPeri(fakeouter, xV, yV, ncell8) + calcPeri(fakeinner, xV, yV, ncell8);
		
		fstart = 2-1;
		fend = 6-1;
		lengthF = sqrt(pow((xV[fstart]-xV[fend]),2) + pow((yV[fstart]-yV[fend]),2));
		
		ftop = 27-1;
		fbot = 36-1;
		lengthFtop = sqrt(pow((xV[fstart]-xV[ftop]),2) + pow((yV[fstart]-yV[ftop]),2));
		lengthFbot = sqrt(pow((xV[fend]-xV[fbot]),2) + pow((yV[fend]-yV[fbot]),2));
		
		if (!runReps)
		{
			bigstringA = bigstringA+"A, "+j+", "+area1+", "+area2+", "+area3+", "+area4+", "+area5+", "+area6+", "+area7+", "+area8+"\n";
			bigstringP = bigstringP+"P, "+j+", "+peri1+", "+peri2+", "+peri3+", "+peri4+", "+peri5+", "+peri6+", "+peri7+", "+peri8+"\n";
			bigstringPressure = bigstringPressure +"Pressure, "+j+", "+kA1*(area1-area1i)+", "+kA2*(area2-area2i)+", "+kA3*(area3-area3i)+", "+kA4*(area4-area4i)+", "+kA5*(area5-area5i)+", "+kA6*(area6-area6i)+", "+kA7*(area7-area7i)+", "+kA8*(area8-area8i)+"\n";
			bigstringTension = bigstringTension +"Tension, "+j+", "+kJ1*(peri1-peri1i)+", "+kJ2*(peri2-peri2i)+", "+kJ3*(peri3-peri3i)+", "+kJ4*(peri4-peri4i)+", "+kJ5*(peri5-peri5i)+", "+kJ6*(peri6-peri6i)+", "+kJ7*(peri7-peri7i)+", "+kJ8*(peri8-peri8i)+"\n";
			bigstringF = bigstringF+"F, "+j+", "+lengthF+", Ftop, "+lengthFtop+", Fbot, "+lengthFbot+"\n";
		}
		else
		{
			bigstringF = bigstringF+ijk+" F, "+j+", "+lengthF+", Ftop, "+lengthFtop+", Fbot, "+lengthFbot+"\n";
		}
	}
	
	if (!runReps)
	{
		print (bigstringA);
		print (bigstringP);
		print (bigstringTension);
		print (bigstringPressure);
	}
	print (bigstringF);
	
	kspringJ = kspringJ*(1000);
	kspringA = kspringA*(1000*1000);
	kspringT = kspringT*(1000);
	
	setBatchMode(false);
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function VertexDialog()
{
	UseDialog = true;
	if (UseDialog) 
	{
		title = "name of experiment";
    	Dialog.create ("Cytokinesis Vertex Model");
	   	Dialog.addChoice ("Run Type", runTypes);
	  
    	Dialog.addNumber ("Total Time", totT);
    	Dialog.addNumber ("Start Furrowing at:", furrowT); 
    	Dialog.addNumber ("Stop Furrowing at:", furrowOFF); 
    	
    	Dialog.addNumber ("Timestep", dT);	   
    	Dialog.addNumber ("Viscocity", nu);
    	
    	Dialog.addNumber ("Furrowing Force:", furrowF);

    	Dialog.addNumber ("Spring Constant Junctions", kspringJ, 5, 6,"x 10E3");
    	Dialog.addNumber ("Spring Constant Area", kspringA, 5, 6,"x 10E6");
    	Dialog.addNumber ("Spring Constant Fake/Ghost Tether", kspringT, 5, 6,"x 10E3");
    	Dialog.addNumber ("Rest Junction Factor", restJFactor);
    	Dialog.addNumber ("Rest Area Factor", restAFactor);
    	
    	Dialog.addCheckbox ("Increase area before cytokinesis?", grow);
    	Dialog.addNumber ("Start growth at:", growT);
    	Dialog.addNumber ("Multiplier for area growth", areafactor);
    	
    	Dialog.addCheckbox ("Stiffen Neighbors?", stiff);
    	Dialog.addChoice ("Stiffen Type", stiffTypes);
    	Dialog.addNumber ("Time to stiffen neighbor(s)", stifftimeOn);
    	Dialog.addNumber ("Time to end stiff neighbor(s)", stifftimeOff);
    	Dialog.addNumber ("Multiplier - Junction Spring", stiffJfactor);
    	Dialog.addNumber ("Multiplier - Area Spring", stiffAfactor); 
    	
		Dialog.addCheckbox ("RhoA Contract Neighbors?", contract);
		Dialog.addChoice ("Contract Type", contractTypes);
		Dialog.addNumber ("Time to contract neighbor(s)", contracttimeOn);
		Dialog.addNumber ("Time to end contract neighbor(s)", contracttimeOff);
		Dialog.addNumber ("Multiplier - Junction Length", contractJfactor);
		Dialog.addNumber ("Multiplier - Area", contractAfactor);
    	
    	Dialog.addCheckbox ("Show Timelapse?", showSim);
    	Dialog.addCheckbox ("Show Tethers?", showTether);
    	Dialog.addCheckbox ("Show Pressure Vectors?", showPressure);
    	Dialog.addCheckbox ("Show Junction Vectors?", showJunction);
    	
    	Dialog.addCheckbox ("Run Replicate Simulations?", runReps);
    	Dialog.addNumber ("Number of replicates?", nReps);
    	
    	Dialog.show ();
    	
    	runType = Dialog.getChoice();
    	totT = Dialog.getNumber();
    	furrowT = Dialog.getNumber();
    	furrowOFF = Dialog.getNumber();
    	
    	dT = Dialog.getNumber();
    	nu = Dialog.getNumber();
    	furrowF = Dialog.getNumber();
    	
    	kspringJ = Dialog.getNumber();
    	kspringA = Dialog.getNumber();
    	kspringT = Dialog.getNumber();
    	restJFactor = Dialog.getNumber();
    	restAFactor = Dialog.getNumber();
    	
    	grow = Dialog.getCheckbox();
    	growT = Dialog.getNumber();
    	areafactor =  Dialog.getNumber();
    	
    	stiff = Dialog.getCheckbox();
    	stiffType = Dialog.getChoice();
    	stifftimeOn = Dialog.getNumber();
    	stifftimeOff = Dialog.getNumber();
    	stiffJfactor = Dialog.getNumber();
    	stiffAfactor = Dialog.getNumber();
    	
		contract = Dialog.getCheckbox();
		contractType = Dialog.getChoice();
		contracttimeOn = Dialog.getNumber();
		contracttimeOff = Dialog.getNumber();
		contractJfactor = Dialog.getNumber();
    	contractAfactor = Dialog.getNumber();
    	
    	showSim = Dialog.getCheckbox();
    	showTether = Dialog.getCheckbox();
    	showPressure = Dialog.getCheckbox();
    	showJunction = Dialog.getCheckbox();
    	
    	runReps = Dialog.getCheckbox();
    	nReps = Dialog.getNumber();
    	    	    	
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//		loadGeometry establishes the initial model geometry and rest lengths/areas for all elastic elements.
//
//		"geometry" in this case is a fixed configuration of one central dividing cell that is surrounded by 6 immediate neighbors,
//			and a fake cell to maintain appropriate boundary conditions. Each cell and the boundary are defined by a set of 44 points
//			that were manually positioned in an external ROI set. The network consists of four types of elastic elements:
//				1) bicellular junctions surrounding each cell,
//				2) 6 tethers connecting tricellular junctions at two cell intersections to the boundary,
//				3) 12 tethers connecting tricellular junctions along single cells to the boundary,
//				4) 1 cytokinetic furrow, a virtual junction that cuts across the dividing cell.
//
//				Junction segments 1-8 surround the central dividing cell.
//				Junction segments 9-26 surround the 7 cell cluster at the center of the simulation.
//				Junction segments 27-44 form the outer boundary of the fake cell
//		
//  ------------------------------------------------------------------------------------------------------------------------
//

function loadGeometry()
{
	tetherlen = newArray(nTethers);
	tetherleni = newArray(nTethers);

	xV = newArray(nV);
	yV = newArray(nV);
	typeV = newArray(nV);
	
	// Vertices are listed in clockwise order and start from the upper-left most vertex.
	
	// The dividing cell contains two additional vertices, 2 and 6, marking the ends of the future bicellular junction between the resulting daughter cells.

	cell1 = newArray(1, 2, 3, 4, 5, 6, 7, 8);
	ncell1 = 8;
	
	cell2 = newArray(9, 10, 11, 3, 2, 1, 26);
	ncell2 = 7;
	
	cell3 = newArray(11, 12, 13, 14, 4, 3);
	ncell3 = 6;
	
	cell4 = newArray(4, 14, 15, 16, 17, 5);
	ncell4 = 6;
	
	cell5 = newArray(7, 6, 5, 17, 18, 19, 20);
	ncell5 = 7;
	
	cell6 = newArray(23, 8, 7, 20, 21, 22);
	ncell6 = 6;
	
	cell7 = newArray(25, 26, 1, 8, 23, 24);
	ncell7 = 6;
	
	// Vertices on the outer and inner boundary of the fake cell align, for instance, 44 (fakeouter) connects to 9.
	
	fakeouter = newArray(44, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43);
	ncell8 = 18;
	
	fakeinner = newArray(9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26);
	ncell8 = 18;
	
	// Tethers holding the central 7 cells to the outer boundary.
	// Tethers consist of two types:
	// 12 type A tethers hold single cell vertices to the boundary.
	// 6 type B tethers hold cell-cell vertices to the boundary.
	
	// typea and typeb indicate the appropriate tethers between fakeouter and fakeinner vertices
	
	typea = newArray(1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0);
	typea = newArray(0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1);
	
	tetherlen = newArray(18);
	tetherleni = newArray(18);
	
	vFX = newArray(nV);
	vFY = newArray(nV);
	
	vDX = newArray(nV);
	vDY = newArray(nV);
	
	initCytoBox(wid, hei);
	isFirst = true;
	makeTissue(nV);
	
	area1 = calcArea(cell1, xV, yV, ncell1);
	area2 = calcArea(cell2, xV, yV, ncell2);
	area3 = calcArea(cell3, xV, yV, ncell3);
	area4 = calcArea(cell4, xV, yV, ncell4);
	area5 = calcArea(cell5, xV, yV, ncell5);
	area6 = calcArea(cell6, xV, yV, ncell6);
	area7 = calcArea(cell7, xV, yV, ncell7);
	
	area8 = calcArea(fakeouter, xV, yV, ncell8) - calcArea(fakeinner, xV, yV, ncell8);
		
	peri1 = calcPeri(cell1, xV, yV, ncell1);
	peri2 = calcPeri(cell2, xV, yV, ncell2);
	peri3 = calcPeri(cell3, xV, yV, ncell3);	
	peri4 = calcPeri(cell4, xV, yV, ncell4);
	peri5 = calcPeri(cell5, xV, yV, ncell5);
	peri6 = calcPeri(cell6, xV, yV, ncell6);
	peri7 = calcPeri(cell7, xV, yV, ncell7);
		
	peri8 = calcPeri(fakeouter, xV, yV, ncell8) + calcPeri(fakeinner, xV, yV, ncell8);
	
//
//		There are 3 cases for initial conditions:
//
//		a) Tissue initially in extension, i.e. their perimeters are shorter than rest values, their areas are smaller than
//		than their rest areas.
//		(area < areai; peri < perii)
//
//		b) Tissue initially in compression, perimeters and areas are larger than rest areas.
//		(area > areai; peri > perii)
//
//		c) Tensegrity!  compression, as areas are larger than than rest and extension  as perimeters are smaller than rest case. 
//		(area_init > area; peri_ini > perimeter)
//
//
// cell wants to be larger, 1.1*area is "compression" ---- alt ----- cell wants to be smaller, 0.8*area is "extension"	
//

//
// Record initial rest areas and rest perimeters. Use these "init" values to restore after optogenetic stimulation
//
	initarea1 = area1i = restAFactor*area1;
	initarea2 = area2i = restAFactor*area2;
	initarea3 = area3i = restAFactor*area3;
	initarea4 = area4i = restAFactor*area4;
	initarea5 = area5i = restAFactor*area5;
	initarea6 = area6i = restAFactor*area6;
	initarea7 = area7i = restAFactor*area7;
	initarea8 = area8i = restAFactor*area8;

	initperi1 = peri1i = restJFactor * peri1;
	initperi2 = peri2i = restJFactor * peri2;
	initperi3 = peri3i = restJFactor * peri3;
	initperi4 = peri4i = restJFactor * peri4;
	initperi5 = peri5i = restJFactor * peri5;
	initperi6 = peri6i = restJFactor * peri6;
	initperi7 = peri7i = restJFactor * peri7;
	initperi8 = peri8i = restJFactor * peri8;
	
	calcTetherLength();
	
	for (k= 0; k<(18); k++)
	{
		tetherleni[k] = 1.0*tetherlen[k]; // start with tethers at rest 1.0, previously they were under tension 0.8
	}
}
//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function zeroForce(vFX, vFY)
{
	for (k= 0; k<(44); k++)
	{
		vFX[k] = 0.0;
		vFY[k] = 0.0;
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function zeroDisp(vDX, vDY)
{
	for (k= 0; k<(44); k++)
	{
		vDX[k] = 0.0;
		vDY[k] = 0.0;
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcTetherForce(kspring, vFX, vFY)
{
	for (k= 0; k<(18); k++)
	{
		tetherX = 0.0;
		tetherY = 0.0;
		
		kin = fakeinner[k]-1;
		kout = fakeouter[k]-1;
		a = pow((xV[kin]-xV[kout]), 2);
		b = pow((yV[kin]-yV[kout]), 2);
		
		tetherlen[k] = pow((a + b), 0.5);
		
		tetherX = kspring*(tetherlen[k]-tetherleni[k])*(xV[kin]-xV[kout])/(tetherleni[k]);
		tetherY = kspring*(tetherlen[k]-tetherleni[k])*(yV[kin]-yV[kout])/(tetherleni[k]);
		
		vFX[kin] = vFX[kin] - tetherX;
		vFY[kin] = vFY[kin] - tetherY;
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcAllJunctionForce(k1, k2, k3, k4, k5, k6, k7, k8, vFX, vFY)
{
	calcJunctionForce(k1, cell1, peri1i, peri1, ncell1, vFX, vFY);
	calcJunctionForce(k2, cell2, peri2i, peri2, ncell2, vFX, vFY);
	calcJunctionForce(k3, cell3, peri3i, peri3, ncell3, vFX, vFY);
	calcJunctionForce(k4, cell4, peri4i, peri4, ncell4, vFX, vFY);
	calcJunctionForce(k5, cell5, peri5i, peri5, ncell5, vFX, vFY);
	calcJunctionForce(k6, cell6, peri6i, peri6, ncell6, vFX, vFY);
	calcJunctionForce(k7, cell7, peri7i, peri7, ncell7, vFX, vFY);
	
	calcJunctionForce(k8, fakeinner, peri8i, peri8, ncell8, vFX, vFY);
}

function calcJunctionForce(scale, cell, perii, peri, numV, vFX, vFY)
{
	for (i= 0; i<(numV-1); i++)
	{
		j = cell[i]-1;
		k = cell[i+1]-1;
		x1 = xV[j];
		y1 = yV[j];
		x2 = xV[k];
		y2 = yV[k];
		
//		kscale = scale*(peri-perii)/perii;
		kscale = scale*(peri-perii);
		
		if (kscale < 0)
		{
//			print("WARNING: COMPRESSION in between vertex: "+j+" and vertex: "+k);
			kscale = 0;
		}
		delx = (x2 - x1);
		dely = (y2 - y1);
		r = sqrt(delx*delx + dely*dely);
		
		vectorX = kscale*(delx/r);
		vectorY = kscale*(dely/r);
		
		//
		// two force vectors -- one from j to k, and another from k to j.
		//
		
		vFX[j] = vFX[j] + vectorX;
		vFY[j] = vFY[j] + vectorY;
		vFX[k] = vFX[k] - vectorX;
		vFY[k] = vFY[k] - vectorY;
	}
	
	j = cell[numV-1]-1;
	k = cell[0]-1;
	
	x1 = xV[j];
	y1 = yV[j];
	x2 = xV[k];
	y2 = yV[k];
			
//	kscale = scale*(peri-perii)/perii;
	kscale = scale*(peri-perii);
	
	if (kscale < 0)
	{
//		print("WARNING: COMPRESSION in between vertex: "+j+" and vertex: "+k);
		kscale = 0;
	}
			
	delx = (x2 - x1);
	dely = (y2 - y1);
	r = sqrt(delx*delx + dely*dely);

	vectorX = kscale*(delx/r);
	vectorY = kscale*(dely/r);

	//
	// two force vectors -- one from j to k, and another from k to j.
	//
		vFX[j] = vFX[j] + vectorX;
		vFY[j] = vFY[j] + vectorY;
		vFX[k] = vFX[k] - vectorX;
		vFY[k] = vFY[k] - vectorY;
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcAllCellPressure(k1, k2, k3, k4, k5, k6, k7, k8)
{
	calcOneCellPressure(k1, area1i, area1, cell1, ncell1, vFX, vFY);
	calcOneCellPressure(k2, area2i, area2, cell2, ncell2, vFX, vFY);
	calcOneCellPressure(k3, area3i, area3, cell3, ncell3, vFX, vFY);
	calcOneCellPressure(k4, area4i, area4, cell4, ncell4, vFX, vFY);
	calcOneCellPressure(k5, area5i, area5, cell5, ncell5, vFX, vFY);
	calcOneCellPressure(k6, area6i, area6, cell6, ncell6, vFX, vFY);
	calcOneCellPressure(k7, area7i, area7, cell7, ncell7, vFX, vFY);
	
	calcOneCellPressure(-k8, area8i, area8, fakeinner, ncell8, vFX, vFY);
}

function calcOneCellPressure(kscale, areai, area, cell, ncell, vFX, vFY)
{
//
// draw perps for each segment in the central cell - cell1[ ], and ncell1
//

//	scale = kscale*(area - areai)/areai;
	scale = kscale*(area - areai);	
	
//	bigstringPressure = bigstringPressure +", "+scale;
	p1 =  cell[ncell-1]-1;
	
	for (k= 0; k<(ncell-1); k++)
	{
		k1 = ncell-1;
		if (k>0)	k1 = k-1;
		k3 = k+1;

		p1 = cell[k1]-1;
		p2 = cell[k] - 1;
		p3 = cell[k3] - 1;
		
		x1 = xV[p1];
		y1 = yV[p1];
		x2 = xV[p2];
		y2 = yV[p2];
		x3 = xV[p3];
		y3 = yV[p3];
		
		delXmin = (y1-y2);
		delYmin = (x2-x1);
		delXplu = (y2-y3);
		delYplu = (x3-x2);
		
		vectorX = scale*(delXmin + delXplu)/2;
		vectorY = scale*(delYmin + delYplu)/2;
		
		vFX[p2] = vFX[p2] + vectorX;
		vFY[p2] = vFY[p2] + vectorY;
	}
	
	k1 = ncell-2;
	k = ncell-1;
	k3 = 0;

	p1 = cell[k1] - 1;
	p2 = cell[k] - 1;
	p3 = cell[k3] - 1;
		
	x1 = xV[p1];
	y1 = yV[p1];
	x2 = xV[p2];
	y2 = yV[p2];
	x3 = xV[p3];
	y3 = yV[p3];
	
	delXmin = (y1-y2);
	delYmin = (x2-x1);
	delXplu = (y2-y3);
	delYplu = (x3-x2);
	
	vectorX = scale*(delXmin + delXplu)/2;
	vectorY = scale*(delYmin + delYplu)/2;

	vFX[p2] = vFX[p2] + vectorX;
	vFY[p2] = vFY[p2] + vectorY;
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcDisp(dT, nu, vFX, vFY, vDX, vDY)
{
	for (k= 0; k<(44); k++)
	{
		vDX[k] = vDX[k] + (dT/nu)*vFX[k];
		vDY[k] = vDY[k] + (dT/nu)*vFY[k];
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//		randomly displace cell vertices, do not move fake outer vertices.
//  ------------------------------------------------------------------------------------------------------------------------
//

function randmoveVX(nV, vDX, vDY)
{
	maxpix = 1;
	for (i=0; i<=nV; i++) 
	{
		vDX[i] = vDX[i] + (maxpix/2)*(random("gaussian")) - (maxpix/2)*(random("gaussian"));
		vDY[i] = vDY[i] + (maxpix/2)*(random("gaussian")) - (maxpix/2)*(random("gaussian"));
	}
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//		Move all cell vertices according to the accumulated displacements, but do not move fake outer vertices. Move includes all displacements.
//  ------------------------------------------------------------------------------------------------------------------------
//

function moveVx(nV, vDX, vDY)
{
	ncellvertices = nV;
	for (i=0; i<=ncellvertices; i++) 
	{
		xV[i] = xV[i] + vDX[i];
		yV[i] = yV[i] + vDY[i];
	}
}

function drawMoveVx(nV, vDX, vDY, Rcolor, Gcolor, Bcolor)
{
	scale = 50;
	ncellvertices = nV;
	for (i=0; i<=ncellvertices; i++) 
	{
		x1 = xV[i];
		y1 = yV[i];
		dx1 = vDX[i];
		dy1 = vDY[i];
		r = sqrt(dx1*dx1 + dy1*dy1);
		
		vectorX = scale*dx1/r;
		vectorY = scale*dy1/r;
		makeArrow(x1, y1, x1+vectorX, y1+vectorY, "small open");	
		run("Fill", "slice");
		run("Select None");
	}
}
//
//  ------------------------------------------------------------------------------------------------------------------------
//		Move furrow vertices with cytokinetic force. As a cell vertex, furrow vertex positions depend furrow force and loads from other elements.
//  ------------------------------------------------------------------------------------------------------------------------
//

function moveFx(dFXdT, dFYdT)
{
	fstart = 2-1;
	fend = 6-1;

	xV[fstart] = xV[fstart] - dFXdT;
	yV[fstart] = yV[fstart] - dFYdT;
		
	xV[fend] = xV[fend] + dFXdT;
	yV[fend] = yV[fend] + dFYdT;
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//  Make the tissue -- read in specific ROI file that contains the 7 central cells.
//  ------------------------------------------------------------------------------------------------------------------------
//

function makeTissue(nV)
{
	myROI = localdir+sep+"Seven Hex Cells 44 nodes.zip";
	roiManager("Open", myROI);
		
	for (i=0; i<nV; i++) 
	{
		roiManager("Select", i);
		Roi.getCoordinates(x, y);
		xV[i] = x[0];
		yV[i] = y[0];
	}
	
	selectWindow("ROI Manager");
	run("Close");
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//  Make the image window to contain the cytokinesis animation.
//  ------------------------------------------------------------------------------------------------------------------------
//

function initCytoBox(length, width) 
{
	if (isOpen("Cytokinesis"))
	{ 
		selectWindow("Cytokinesis"); close();
	}
	newImage("Cytokinesis", "RGB Black", width, length, 1);
	myCytoBox = getTitle();
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//	Calculate the current area of the cell.
//  ------------------------------------------------------------------------------------------------------------------------
//
// Points are (x1, y1), (x2, y2), ..., (x4, y4), then Gauss's Shoelace Formula: 2A = (x1y2 - x2y1) + (x2y3 - x3y2) + ...
//

function calcArea(cell, xV, yV, numV)
{
//	print ("New Cell for Area");
	area = 0;
	for (i= 0; i<(numV-1); i++)
	{
		k = cell[i]-1;
		j = cell[i+1]-1;
		delarea = xV[k]*yV[j]-xV[j]*yV[k];
		area = area + delarea;
		
	}
	k = cell[numV-1]-1;
	j = cell[0]-1;
	delarea = xV[k]*yV[j]-xV[j]*yV[k];
	area = area + delarea;
	
	return area/2;
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//  Calculate the current perimeter, or sum of the junction lengths of the cell.
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcPeri(cell, xV, yV, numV)
{
//	print ("New Cell for Perimeter");
	leng = 0;
	for (i= 0; i<(numV-2); i++)
	{
		k = cell[i]-1;
		j = cell[i+1]-1;
		a = pow((xV[j]-xV[k]), 2);
		b = pow((yV[j]-yV[k]), 2);
		
		delleng = pow((a + b), 0.5);
		leng = leng + delleng;
		
	}
	
	k = cell[numV-1]-1;
	j = cell[0]-1;
	
	a = pow((xV[j]-xV[k]), 2);
	b = pow((yV[j]-yV[k]), 2);
	delleng = pow((a + b), 0.5);
	leng = leng + delleng;
		
	return leng;
}

//
//  ------------------------------------------------------------------------------------------------------------------------
//	Calculate length of the tethers that connect the central 7 cells to the outer ring.
//  ------------------------------------------------------------------------------------------------------------------------
//

function calcTetherLength()
{
	for (k= 0; k<(18); k++)
	{
		kin = fakeinner[k]-1;
		kout = fakeouter[k]-1;
		a = pow((xV[kin]-xV[kout]), 2);
		b = pow((yV[kin]-yV[kout]), 2);
		tetherlen[k] = pow((a + b), 0.5);	
	}
}
	
//
//  ------------------------------------------------------------------------------------------------------------------------
//	Create the file names for the simulation output file.
//  ------------------------------------------------------------------------------------------------------------------------
//

function outputPrefix()
{
     MonthNames = newArray("Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec");
     DayNames = newArray("Sun", "Mon","Tue","Wed","Thu","Fri","Sat");
     getDateAndTime(year, month, dayOfWeek, dayOfMonth, hour, minute, second, msec);
     preFix =DayNames[dayOfWeek]+"_";
     if (dayOfMonth<10) {preFix = preFix+"0";}
     preFix = preFix +dayOfMonth+"_"+MonthNames[month]+"_"+year+"__ ";
     if (hour<10) {preFixg = preFix+"0";}
     preFix = preFix+hour+"_";
     if (minute<10) {preFix = preFix+"0";}
     preFix = preFix+minute+"_";
     if (second<10) {preFix = preFix+"0";}
     preFix = preFix+second;
     return preFix;
 }
//
//  ------------------------------------------------------------------------------------------------------------------------
//	Draw the tissue into the animation file. In addition, write the simulation parameters into the image and log files.
//  ------------------------------------------------------------------------------------------------------------------------
//

function drawGeometry()
{
	selectWindow(myCytoBox);
	if (isFirst)
	{
		isFirst = false;
	}
	else
	{
		run("Add Slice");
	}
	
	drawCell(cell2, ncell2, 2, 0, 210, 0, "Fill", false, star2); // (0, 210, 0) "green"
	drawCell(cell3, ncell3, 2, 0, 210, 0, "Fill", false, star3); // (0, 210, 0) "green"
	drawCell(cell4, ncell4, 2, 0, 210, 0, "Fill", false, star4); // (0, 210, 0) "green"
	drawCell(cell5, ncell5, 2, 0, 210, 0, "Fill", false, star5); // (0, 210, 0) "green"
	drawCell(cell6, ncell6, 2, 0, 210, 0, "Fill", false, star6); // (0, 210, 0) "green"
	drawCell(cell7, ncell7, 2, 0, 210, 0, "Fill", false, star7); // (0, 210, 0) "green"
	
	drawCell(cell1, ncell1, 3, 210, 30, 210, "Fill", true, star1); // (220, 30, 220) "magenta"
		
}
function printParameters()
{
	var paramString;
	
	paramString = "Tot Time: "+totT+" dT: "+dT+" nu: "+nu+" Start Furr: "+furrowT+" Stop Furr: "+furrowOFF+" Furr Force: "+furrowF;
	if (grow) paramString = paramString+" Grow at: "+growT+" Grow Area: "+areafactor;
	print ("## "+paramString);
	
	paramString = "Junct spring: "+kspringJ+" Area spring: "+kspringA+" Tether Spring: "+kspringT+" Cell's Rest Area Factor: "+restAFactor+" Cells' Rest Perimeter Factor: "+restJFactor;
	print ("## "+paramString);
	
	if (stiff) 
	{
		paramString = "Change Stiffness of "+stiffType+" starting at: "+stifftimeOn+" ending at: "+stifftimeOff+" mult J stiff: "+stiffJfactor+" mult A stiff: "+stiffAfactor;
		print ("## "+paramString);
	}
	if (contract) 
	{
		paramString = "Optogenetic contraction of "+contractType+" starting at: "+contracttimeOn+" ending at: "+contracttimeOff+" mult J contract: "+contractJfactor+" mult A contract: "+contractAfactor;
		print ("## "+paramString);
	}
}

function drawParameters()
{
	var paramString;
	setFont("SansSerif", 14);
	setForegroundColor(255,255,0);
	selectWindow(myCytoBox);
	
	atY = 20;

	paramString = "Tot Time: "+totT+" dT: "+dT+" nu: "+nu+" Start Furr: "+furrowT+" Stop Furr: "+furrowOFF+" Furr Force: "+furrowF;
	if (grow) paramString = paramString+" Grow at: "+growT+" Grow Area: "+areafactor;
	drawString(paramString, 10, atY);
	atY = atY + 20;
	
	paramString = "Junct spring: "+kspringJ+" Area spring: "+kspringA+" Tether Spring: "+kspringT+" Cell's Rest Area Factor: "+restAFactor+" Cells' Rest Perimeter Factor: "+restJFactor;
	drawString(paramString, 10, atY);
	atY = atY + 20;
	
	if (stiff) 
	{
		paramString = "Change Stiffness of "+stiffType+" starting at: "+stifftimeOn+" ending at: "+stifftimeOff+" mult J stiff: "+stiffJfactor+" mult A stiff: "+stiffAfactor;
		drawString(paramString, 10, atY);
		atY = atY + 20;
	}
	if (contract) 
	{
		paramString = "Optogenetic contraction of "+contractType+" starting at: "+contracttimeOn+" ending at: "+contracttimeOff+" mult J contract: "+contractJfactor+" mult A contract: "+contractAfactor;
		drawString(paramString, 10, atY);
	}

}

//
//  ------------------------------------------------------------------------------------------------------------------------
//	Draw the cells and extra graphical elements into the animation file.
//  ------------------------------------------------------------------------------------------------------------------------
//

function drawCell(cell, numV, linewidth, Rcolor, Bcolor, Gcolor, lineorfill, furrow, star)
{

	//
	// draw central dividing cell - cellA
	//

	setForegroundColor(Rcolor, Bcolor, Gcolor); // (220, 0, 220) "magenta"
	
	xcen = 0.;
	ycen = 0.;

	for (i= 0; i<(numV-1); i++)
	{
		j = cell[i]-1;
		k = cell[i+1]-1;
		x1 = xV[j];
		y1 = yV[j];
		x2 = xV[k];
		y2 = yV[k];
		makeLine(x1, y1, x2, y2, linewidth);
		run(lineorfill, "slice");
		xcen = xcen + x1;
		ycen = ycen + y1;
	}
	
	j = cell[numV-1]-1;
	k = cell[0]-1;
	
	x1 = xV[j];
	y1 = yV[j];
	x2 = xV[k];
	y2 = yV[k];
	makeLine(x1, y1, x2, y2, linewidth);
	run(lineorfill, "slice");
	run("Select None");
	
	xcen = (xcen + x1)/numV;
	ycen = (ycen + y1)/numV;
	
	if (dFdT > 0 && furrow) drawOval(10, 90, 30,30);
	
	if (star) fillOval(xcen, ycen, 20, 20);
	
}

function drawTethers(linewidth, Rcolor, Bcolor, Gcolor)
{
	selectWindow(myCytoBox);
	
	setForegroundColor(Rcolor, Bcolor, Gcolor); // (220, 0, 220) "magenta"
	
	for(k=0;k<18;k++)
	{
		kin = fakeinner[k]-1;
		kout = fakeouter[k]-1;
		drawOval(xV[kin]-4, yV[kin]-4, 8, 8);
		drawOval(xV[kout]-4, yV[kout]-4, 8, 8);
		makeLine(xV[kin], yV[kin], xV[kout], yV[kout]);
		run("Fill", "slice");	
		run("Select None");
	}
}

function drawPerps(Rcolor, Bcolor, Gcolor)
{

//
//	draw vectors representing the pressure for each segment in the fake cell
//
	setForegroundColor(255, 105, 0); // (221,160,221) "orange"
	
	p1 = fakeinner[17]-1;
	
	for(k=0;k<18;k++)
	{
		p2 = fakeinner[k]-1;
		drawOnePerp(xV[p1], yV[p1], xV[p2], yV[p2], "small open");
		p1 = p2;
	}

//
// draw vectors representing the pressure for each segment in the central cell - cell1[ ], and ncell1
//

	setForegroundColor(230,230,250); // (230,230,250) "lavender"
		
	p1 = cell1[ncell1-1]-1;
	
	for (k= 0; k<(ncell1); k++)
	{
		p2 = cell1[k]-1;
		drawOnePerp(xV[p1], yV[p1], xV[p2], yV[p2], "small open");
		
		p1 = p2;
	}


}

function drawPressure(kscale, cell, ncell, Rcolor, Bcolor, Gcolor)
{

//
// draw vectors representing the pressure for each segment in the central cell - cell1[ ], and ncell1
//

	setForegroundColor(Rcolor, Bcolor, Gcolor);
	
	scale = 0.5*kscale;
		
	p1 =  cell[ncell-1]-1;
	
	for (k= 0; k<(ncell-1); k++)
	{
		k1 = ncell-1;
		if (k>0)	k1 = k-1;
		k3 = k+1;

		p1 = cell[k1]-1;
		p2 = cell[k] - 1;
		p3 = cell[k3] - 1;
		
		x1 = xV[p1];
		y1 = yV[p1];
		x2 = xV[p2];
		y2 = yV[p2];
		x3 = xV[p3];
		y3 = yV[p3];
		
		delXmin = (y1-y2);
		delYmin = (x2-x1);
		delXplu = (y2-y3);
		delYplu = (x3-x2);
		
		vectorX = scale*(delXmin + delXplu)/2;
		vectorY = scale*(delYmin + delYplu)/2;
		
		makeArrow(x2, y2, x2-vectorX, y2-vectorY, "small open");
		run("Fill", "slice");
		run("Select None");
		
	}
	
	k1 = ncell-2;
	k = ncell-1;
	k3 = 0;

	p1 = cell[k1] - 1;
	p2 = cell[k] - 1;
	p3 = cell[k3] - 1;
		
	x1 = xV[p1];
	y1 = yV[p1];
	x2 = xV[p2];
	y2 = yV[p2];
	x3 = xV[p3];
	y3 = yV[p3];
	
	delXmin = (y1-y2);
	delYmin = (x2-x1);
	delXplu = (y2-y3);
	delYplu = (x3-x2);

	vectorX = scale*(delXmin + delXplu)/2;
	vectorY = scale*(delYmin + delYplu)/2;

	makeArrow(x2, y2, x2-vectorX, y2-vectorY, "small open");
	run("Fill", "slice");
	run("Select None");

}

//
// draw junction tension vectors at each vertex around the cell
//

function drawJ(cell, numV, linwid, Rcolor, Bcolor, Gcolor)
{
	kscale = 25;
	setForegroundColor(Rcolor, Bcolor, Gcolor);
	setLineWidth(linewid);

	for (i= 0; i<(numV-1); i++)
	{
		j = cell[i]-1;
		k = cell[i+1]-1;
		x1 = xV[j];
		y1 = yV[j];
		x2 = xV[k];
		y2 = yV[k];
		
		delx = (x2 - x1);
		dely = (y2 - y1);
		r = sqrt(delx*delx + dely*dely);
		
		vectorX = kscale*(delx/r);
		vectorY = kscale*(dely/r);
		
		//
		// draw two arrows -- one from j to k, and another from k to j.
		//
		
		makeArrow(x1, y1, x1+vectorX, y1+vectorY, "small open");	
		run("Fill", "slice");
		run("Select None");
		
		makeArrow(x2, y2, x2-vectorX, y2-vectorY, "small open");	
		run("Fill", "slice");
		run("Select None");

	}
	
	j = cell[numV-1]-1;
	k = cell[0]-1;
	
	x1 = xV[j];
	y1 = yV[j];
	x2 = xV[k];
	y2 = yV[k];
			
	delx = (x2 - x1);
	dely = (y2 - y1);
	r = sqrt(delx*delx + dely*dely);

	vectorX = kscale*(delx/r);
	vectorY = kscale*(dely/r);

	//
	// draw two arrows -- one from j to k, and another from k to j.
	//

	makeArrow(x1, y1, x1+vectorX, y1+vectorY, "small open");	
	run("Fill", "slice");
	run("Select None");

	makeArrow(x2, y2, x2-vectorX, y2-vectorY, "small open");	
	run("Fill", "slice");
	run("Select None");

}

function drawArrow (x1, y1, dx, dy, arrowtype, arrowlen)
{
	selectWindow(myCytoBox);
	
	r = pow((dx*dx + dy*dy), 0.5);
	x2 = x1 + arrowlen*(dx/r);
	y2 = y1 + arrowlen*(dy/r);

	makeArrow(x1, y1, x2, y2, arrowtype);
	run("Fill", "slice");
	run("Select None");
}

function drawOnePerp(x1, y1, x2, y2, arrowtype)
{
	len = 0.5;
	
	selectWindow(myCytoBox);
	
	midx = (x2+x1)/2;
	midy = (y2+y1)/2;
	
	offx = midx - len*(y2-y1);
	offy = midy + len*(x2-x1);

	makeArrow(midx, midy, offx, offy, arrowtype);
	run("Fill", "slice");
	run("Select None");

}

