# Migration of `Atlas/StatisticalMechanics`

The unconditional headline results of this archived development, and the modules they depend on,
were ported to Lean 4.35.0 / Mathlib v4.35.0 and moved into the root libraries. This table maps each
ported source file to its new module. The rest of this directory is unchanged and stays outside the
root build.

## MathlibExt

| Source file | Module |
| --- | --- |
| `Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean` | `MathlibExt.Probability.Percolation.RussoInfluence` |
| `Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise` |
| `Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean` | `MathlibExt.Probability.Configuration.CondDistribution` |
| `Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean` | `MathlibExt.Probability.Configuration.ConfigSpace` |
| `Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean` | `MathlibExt.Probability.Configuration.CylinderDeriv` |
| `Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean` | `MathlibExt.Probability.Configuration.Ergodicity` |
| `Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned.Basic` |
| `Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned.AE` |
| `Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned.Filling` |
| `Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned` |
| `Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean` | `MathlibExt.Dynamics.Ergodic.KingmanSigned.MaximalErgodic` |
| `Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean` | `MathlibExt.Probability.Configuration.MonotoneLimit` |
| `Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean` | `MathlibExt.Probability.Configuration.ProductMeasure` |
| `Atlas/StatisticalMechanics/Code/Foundations/Prokhorov.lean` | `MathlibExt.Probability.Configuration.Prokhorov` |
| `Atlas/StatisticalMechanics/Code/Foundations/StochasticDomination.lean` | `MathlibExt.Probability.StochasticOrder.StochasticDomination` |
| `Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean` | `MathlibExt.Probability.StochasticOrder.Strassen` |
| `Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean` | `MathlibExt.Probability.StochasticOrder.StrassenFinite` |
| `Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean` | `MathlibExt.Probability.Configuration.WeakConvergence` |
| `Atlas/StatisticalMechanics/Code/Inequalities/BK.lean` | `MathlibExt.Probability.CorrelationInequalities.BK` |
| `Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean` | `MathlibExt.Probability.CorrelationInequalities.DisjointOccurrence` |
| `Atlas/StatisticalMechanics/Code/Inequalities/FKG.lean` | `MathlibExt.Probability.CorrelationInequalities.FKG` |
| `Atlas/StatisticalMechanics/Code/Inequalities/Harris.lean` | `MathlibExt.Probability.CorrelationInequalities.Harris` |
| `Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean` | `MathlibExt.Probability.CorrelationInequalities.IncreasingEvent` |
| `Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean` | `MathlibExt.Probability.CorrelationInequalities.Pivotal` |
| `Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean` | `MathlibExt.Probability.CorrelationInequalities.Reimer` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerMixedMonotone` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerWeightedPairs` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricWeights` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDownCompressionPairs` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerIteratedCompression` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDisjointPairCount` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerSpecialCases` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerFamilyEvents` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerCompression` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDoubled` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDoubledCompression` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDoubledEvents` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerDisjointDetermined` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerStep` |
| `Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean` | `MathlibExt.Probability.CorrelationInequalities.Russo` |
| `Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ArcSides` |
| `Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchStarHull` |
| `Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConditions` |
| `Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume` |
| `Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CanonicalContour` |
| `Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ClosedContourSeparation` |
| `Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters` |
| `Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourAnchor` |
| `Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourLinksExits` |
| `Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalance` |
| `Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity` |
| `Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.Cyclomatic` |
| `Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.DartDef` |
| `Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.DartInjective` |
| `Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.DartNext` |
| `Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.DartOrbit` |
| `Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceDomino` |
| `Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosingLength` |
| `Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerComponentCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerFaces` |
| `Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank` |
| `Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeneral` |
| `Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeometricFaces` |
| `Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FaceComponentBijection` |
| `Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FaceRegion` |
| `Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FloodFillConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice` |
| `Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.InsideConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceOrbit` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanBridgeCycle` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanClusterBridge` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.SeparatingSide` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCrossingCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleRank` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleSpace` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FaithfulEvenPeel` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEulerInduction` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEulerSeparation` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEvenBiconditional` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EvenContourColoring` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanFaithfulCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorReconnect` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanGeneralCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanIsCyclesCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KeepResidueExamples` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KeepReconnectCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanLeftRegionInterior` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RegionGraphAddEdge` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanSingleCycle` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanVeblenPeel` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanVeblenStep` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EdgeFlipClosedContour` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanWindingConstruct` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanZ2` |
| `Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.LeftFace` |
| `Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.MinimalPeriodLoop` |
| `Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHull` |
| `Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.NoPinchDual` |
| `Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.NoPinchMatching` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEncloses` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitExteriorEven` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitInteriorOdd.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitInteriorOdd` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitLoopBridge` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingWitness` |
| `Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.PathVisitsRow` |
| `Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual` |
| `Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric` |
| `Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology` |
| `Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RotationSystemFaces` |
| `Atlas/StatisticalMechanics/Code/Lattice/SegmentConn.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentConn` |
| `Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TreeNoSepEuler` |
| `Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber` |
| `Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TwoPathsCrossWinding` |
| `Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.Umlaufsatz` |
| `Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzSingleCycle` |
| `Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent` |
| `Atlas/StatisticalMechanics/Code/Lattice/Wall1EmbeddingRetry.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FaceMultiplicityOne` |
| `Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.WhitneyBridge` |
| `Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CutColoring` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingColoring` |
| `Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.DirectionWalk` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCornerCountLocal` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellLocalChange` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorEulerBound` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnetLocal` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet` |
| `Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch` |
| `Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.EdgeUnique` |
| `Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticePolygonInterior` |
| `Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz` |
| `Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InsidePropagation` |
| `Atlas/StatisticalMechanics/Code/Onsager/InsideConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TopCornerCellInside` |
| `Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorCells` |
| `Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkPlanarSubgraph` |
| `Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.JordanParity` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.KacWardMatrix` |
| `Atlas/StatisticalMechanics/Code/Onsager/LeftCornerE.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerE` |
| `Atlas/StatisticalMechanics/Code/Onsager/LeftCornerN.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerN` |
| `Atlas/StatisticalMechanics/Code/Onsager/LeftCornerS.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerS` |
| `Atlas/StatisticalMechanics/Code/Onsager/LeftCornerW.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerW` |
| `Atlas/StatisticalMechanics/Code/Onsager/MasterCorner.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CornerWeights` |
| `Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkVertices` |
| `Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TurnCount` |
| `Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.Orientation` |
| `Atlas/StatisticalMechanics/Code/Onsager/PinchFree.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.PinchFree` |
| `Atlas/StatisticalMechanics/Code/Onsager/RayFlipH.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.RayFlipH` |
| `Atlas/StatisticalMechanics/Code/Onsager/RayFlipV.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.RayFlipV` |
| `Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TopRowWestRun` |
| `Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.StraightCorner` |
| `Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TopRow` |
| `Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TurningTelescope` |
| `Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.Umlaufsatz` |
| `Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.ExtremeCorners` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellBoundary` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCellBridge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellBridge` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellLocal` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellRegion` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCornerSum.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCornerSum` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCrossing` |
| `Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCrossingV` |
| `Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean` | `MathlibExt.Probability.Percolation.InfiniteClusterCount` |
| `Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean` | removed during review (duplicate or vacuous); its definition `DiscreteJordanSeparation` was ported in the second round (below) |
| `Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean` | `MathlibExt.Probability.Percolation.CylinderDerivative` |
| `Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean` | `MathlibExt.Probability.Percolation.DctDifferential` |
| `Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean` | `MathlibExt.Probability.Percolation.ConnectionsInsideSet` |
| `Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean` | `MathlibExt.Probability.Percolation.DifferentialInequality` |
| `Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean` | `MathlibExt.Probability.Percolation.DctSurfacePartition` |
| `Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean` | `MathlibExt.Probability.Percolation.Exploration` |
| `Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean` | `MathlibExt.Probability.Percolation.LastExit` |
| `Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean` | `MathlibExt.Probability.Percolation.OffClusterIndep` |
| `Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean` | `MathlibExt.Probability.Percolation.PcNontrivial` |
| `Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean` | `MathlibExt.Probability.Percolation.PcUpper` |
| `Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean` | `MathlibExt.Probability.Percolation.PcUpperEnclosure` |
| `Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean` | `MathlibExt.Probability.Percolation.SharpnessFromInputs` |
| `Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean` | `MathlibExt.Probability.Percolation.SharpnessTheorem` |
| `Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean` | `MathlibExt.Probability.Percolation.SubcriticalDecay` |
| `Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean` | `MathlibExt.Probability.Percolation.TranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean` | `MathlibExt.Probability.Percolation.SurfaceReassembly` |
| `Atlas/StatisticalMechanics/Code/Percolation/Theta.lean` | `MathlibExt.Probability.Percolation.Theta` |
| `Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean` | `MathlibExt.Probability.Percolation.TildePc` |
| `Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean` | `MathlibExt.Probability.Hypercontractivity.BonamiTensorize` |
| `Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean` | `MathlibExt.Probability.Hypercontractivity.BonamiTwoPoint` |
| `Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean` | `MathlibExt.Probability.CorrelationInequalities.InfiniteBK` |
| `Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean` | `MathlibExt.Probability.CorrelationInequalities.InfiniteHarris` |
| `Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean` | `MathlibExt.Probability.CorrelationInequalities.InhomogeneousBK` |
| `Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean` | `MathlibExt.Probability.Hypercontractivity.PBiasedConvexity` |
| `Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean` | `MathlibExt.Probability.Hypercontractivity.PBiasedIntegralHC` |
| `Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean` | `MathlibExt.Probability.Hypercontractivity.PBiasedTwoPoint` |
| `Atlas/StatisticalMechanics/Code/Probability/VectorTwoPoint.lean` | `MathlibExt.Probability.Hypercontractivity.VectorTwoPoint` |
| `Atlas/StatisticalMechanics/Code/RSW/Defs.lean` | `MathlibExt.Probability.Percolation.RSW.Defs` |
| `Atlas/StatisticalMechanics/Code/RSW/Strip.lean` | `MathlibExt.Probability.Percolation.RSW.Strip` |
| `Atlas/StatisticalMechanics/Code/SLE/Defs.lean` | `MathlibExt.Analysis.Complex.Loewner.Defs` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerExistence` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerODE` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerProps` |
| `Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean` | `MathlibExt.Probability.Percolation.PivotalFactor` |
| `Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.Crossings` |
| `Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean` | `MathlibExt.Probability.Percolation.SharpThresholdKKL` |
| `Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean` | `MathlibExt.Probability.Percolation.SharpThreshold` |
| `Atlas/StatisticalMechanics/Code/Universality/Defs.lean` | `MathlibExt.Probability.Percolation.Universality.Defs` |
| `Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean` | `MathlibExt.Probability.Percolation.Universality.HVIntersection` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean` | `MathlibExt.Probability.Percolation.Universality.RSWStrip` |
| `Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean` | `MathlibExt.Probability.Percolation.Universality.VSeparates` |
| `Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean` | `MathlibExt.Probability.Percolation.Universality.CrossingSeparation` |
| `Atlas/StatisticalMechanics/Code/Walls/euceuler.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CellEulerCharacteristic` |
| `Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.AngleDefect` |

## CSLibExt

| Source file | Module |
| --- | --- |
| `Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean` | `CSLibExt.Complexity.BooleanFunctions.OSSS` |
| `Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean` | `CSLibExt.Complexity.BooleanFunctions.Poincare` |
| `Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.BourgainPerCoord` |
| `Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean` | `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC` |
| `Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.DegreeTruncation` |
| `Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.EntropySubadd` |
| `Atlas/StatisticalMechanics/Code/Probability/FSMartingale.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.FSMartingale` |
| `Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.FSPerEdge` |
| `Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.FSRhoOptimise` |
| `Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean` | `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC` |
| `Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality` |
| `Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogOptimisation` |
| `Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogSobolev` |
| `Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLfromHC` |
| `Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLpBiased` |
| `Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.MaxElementDecomp` |
| `Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean` | `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize` |
| `Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform` |
| `Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean` | `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CappedExponentGap` |
| `Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean` | `CSLibExt.Complexity.BooleanFunctions.KKL.KKLEvents` |

## PhyslibExt

| Source file | Module |
| --- | --- |
| `Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualCritical` |
| `Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue` |
| `Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.AdditiveGluing` |
| `Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.AvgDensityCollapse` |
| `Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryDecay` |
| `Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryInfluenceDecay` |
| `Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxCrossGraph` |
| `Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreeEnergyNearSubadditive` |
| `Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreeEnergyDyadic` |
| `Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreeWiredClusterCount` |
| `Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxTailLimit` |
| `Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxTiling` |
| `Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.CenteredFreeEnergy` |
| `Atlas/StatisticalMechanics/Code/FK/Comparison.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Comparison` |
| `Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ComparisonHolley` |
| `Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ConvexDerivLimit` |
| `Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint` |
| `Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredErgodicity` |
| `Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvarianceFromHomogeneity` |
| `Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DecayOfCorrelations` |
| `Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DensityBounds` |
| `Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DensityFiniteToInfinite` |
| `Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DisjointBoxFactorization` |
| `Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DlrSandwich` |
| `Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.DomainMarkov` |
| `Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction` |
| `Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginal` |
| `Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdwardsSokal` |
| `Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.PottsCorrelation` |
| `Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicIsExtreme` |
| `Atlas/StatisticalMechanics/Code/FK/Ergodicity.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity` |
| `Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EsCorrelations` |
| `Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKDensityDeriv` |
| `Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxDomainMarkov` |
| `Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxReduce` |
| `Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ExtremeIsErgodic` |
| `Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolumeTranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/FKG.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKG` |
| `Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessGeneralQ` |
| `Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKInterfaceSubadd` |
| `Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredTranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicOfMixing` |
| `Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicOfUpperDecay` |
| `Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKPressureDeriv` |
| `Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKTwoBoxDecoupling` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKUniqPerEdge` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniqPrimitives.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxSurfaceRatio` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeDensityQ2` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneInPBoundaryCondition` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose3.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKUniquenessDensity` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessOffCountable` |
| `Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromFreeEnergy` |
| `Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FKWiredDomainMonotone` |
| `Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FeketeLimit` |
| `Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FiniteEnergy` |
| `Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FiniteVolumeShift` |
| `Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreePercolationAbovePc` |
| `Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.FreeWeakLimit` |
| `Atlas/StatisticalMechanics/Code/FK/GenuineEdgeCollapse.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.GenuineEdgeCollapse` |
| `Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.HolleyCoupling` |
| `Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.IVPressureConvex` |
| `Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.IVTranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/InducedBC.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.InducedBC` |
| `Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume` |
| `Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeIndicatorShiftDecay` |
| `Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.IntegralShiftDecay` |
| `Atlas/StatisticalMechanics/Code/FK/IvProperties.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties` |
| `Atlas/StatisticalMechanics/Code/FK/IvPropertiesFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolumeFKG` |
| `Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.LimitCommutation` |
| `Atlas/StatisticalMechanics/Code/FK/Limits.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Limits` |
| `Atlas/StatisticalMechanics/Code/FK/LimitsInfinite.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.LimitsInfinite` |
| `Atlas/StatisticalMechanics/Code/FK/MonoBC.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC` |
| `Atlas/StatisticalMechanics/Code/FK/MonotoneVolumeLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneVolumeLimit` |
| `Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit` |
| `Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.MultiEdgeDecay` |
| `Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreCarrier` |
| `Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination` |
| `Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreSandwich` |
| `Atlas/StatisticalMechanics/Code/FK/OneSidedContinuity.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.OneSidedContinuity` |
| `Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.OrderTransition` |
| `Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial` |
| `Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.PcLtOnePeierls` |
| `Atlas/StatisticalMechanics/Code/FK/Potts.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Potts` |
| `Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.PressureDiff` |
| `Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.QuadrantPartition` |
| `Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster` |
| `Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.RotationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivativeBeta` |
| `Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivativeBetaSum` |
| `Atlas/StatisticalMechanics/Code/FK/SecantClose.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.LogitFreeEnergyComparison` |
| `Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.SpatialCollapse` |
| `Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.SuperMultiplicative` |
| `Atlas/StatisticalMechanics/Code/FK/TailLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TailLimit` |
| `Atlas/StatisticalMechanics/Code/FK/ThetaZeroBelowPc.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc` |
| `Atlas/StatisticalMechanics/Code/FK/Tilt.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Tilt` |
| `Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TiltSecant` |
| `Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TranslationCofinal` |
| `Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TwoPoint` |
| `Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointInfinite` |
| `Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointConnectivity` |
| `Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.UniformBulkDeviation` |
| `Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.Uniqueness` |
| `Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredBoxLimit` |
| `Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain` |
| `Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredDominationInner` |
| `Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.WiredPressureDeriv` |
| `Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean` | `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangAsano` |
| `Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean` | `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangDisjointUnion` |
| `Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean` | `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge` |
| `Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean` | `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial` |
| `Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean` | `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSymmetry` |
| `Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.InvariantEventsTail` |
| `Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateZeroOne` |
| `Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean` | `PhyslibExt.CondensedMatter.IsingModel.AizenmanBarsky` |
| `Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean` | `PhyslibExt.CondensedMatter.IsingModel.AizenmanHdom` |
| `Atlas/StatisticalMechanics/Code/Ising/AizenmanInclusionExclusion.lean` | `PhyslibExt.CondensedMatter.IsingModel.AizenmanInclusionExclusion` |
| `Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean` | `PhyslibExt.CondensedMatter.IsingModel.AizenmanSignDominance` |
| `Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean` | `PhyslibExt.CondensedMatter.IsingModel.AizenmanTrueBackbone` |
| `Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean` | `PhyslibExt.CondensedMatter.IsingModel.CorrelationRatio` |
| `Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean` | `PhyslibExt.CondensedMatter.IsingModel.CurrentWeight` |
| `Atlas/StatisticalMechanics/Code/Ising/DLR.lean` | `PhyslibExt.CondensedMatter.IsingModel.DLR` |
| `Atlas/StatisticalMechanics/Code/Ising/EvenSubgraphDecomp.lean` | `PhyslibExt.CondensedMatter.IsingModel.KWClosedWalkParity` |
| `Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateDLRConsistency` |
| `Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean` | `PhyslibExt.CondensedMatter.IsingModel.FiniteVolumeDomain` |
| `Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean` | `PhyslibExt.CondensedMatter.IsingModel.FiniteVolumeRelabel` |
| `Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean` | `PhyslibExt.CondensedMatter.IsingModel.FiniteVolumeSum` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSDistinctSite` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSDuplicateVariable` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSInhomVertexPartition` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSInhomogeneous` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSLebowitz` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSThreePoint` |
| `Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean` | `PhyslibExt.CondensedMatter.IsingModel.GHSVertexPartition` |
| `Atlas/StatisticalMechanics/Code/Ising/GKS.lean` | `PhyslibExt.CondensedMatter.IsingModel.GKS` |
| `Atlas/StatisticalMechanics/Code/Ising/GKS2.lean` | `PhyslibExt.CondensedMatter.IsingModel.GKS2` |
| `Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean` | `PhyslibExt.CondensedMatter.IsingModel.Gibbs` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean` | `PhyslibExt.CondensedMatter.IsingModel.GibbsChoquet` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsExtreme.lean` | `PhyslibExt.CondensedMatter.IsingModel.GibbsExtreme` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateExtremeErgodic` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean` | `PhyslibExt.CondensedMatter.IsingModel.GibbsSimplex` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean` | `PhyslibExt.CondensedMatter.IsingModel.GibbsSimplexInfinite` |
| `Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexUncond.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateErgodicOfDecay` |
| `Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean` | `PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean` | `PhyslibExt.CondensedMatter.IsingModel.IsingBoxSqueeze` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateUpperDecay` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingFKGLayer.lean` | `PhyslibExt.CondensedMatter.IsingModel.IsingFKGLayer` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateErgodicOfUpperDecay` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateTIOfHomogeneous` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateErgodic` |
| `Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateTranslatedBoxes` |
| `Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean` | `PhyslibExt.CondensedMatter.IsingModel.KWClosedWalkParity` |
| `Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean` | `PhyslibExt.CondensedMatter.IsingModel.KWDualBijection` |
| `Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean` | `PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality` |
| `Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.KramersWannierCutMatching` |
| `Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean` | `PhyslibExt.CondensedMatter.IsingModel.KramersWannierDuality` |
| `Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean` | `PhyslibExt.CondensedMatter.IsingModel.KramersWannierEvenToCut` |
| `Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean` | `PhyslibExt.CondensedMatter.IsingModel.KramersWannierGeneral` |
| `Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean` | `PhyslibExt.CondensedMatter.IsingModel.MagNonneg` |
| `Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean` | `PhyslibExt.CondensedMatter.IsingModel.Magnetization` |
| `Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsSquareLattice` |
| `Atlas/StatisticalMechanics/Code/Ising/Peierls.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsConnectedCount` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsOriginClusters` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsContourCount` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsCriterion` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsHoleFree` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsOuterContour` |
| `Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean` | `PhyslibExt.CondensedMatter.IsingModel.PeierlsContours` |
| `Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateDLR` |
| `Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateTI` |
| `Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.PlusStateTICylinder` |
| `Atlas/StatisticalMechanics/Code/Ising/Pressure.lean` | `PhyslibExt.CondensedMatter.IsingModel.Pressure` |
| `Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean` | `PhyslibExt.CondensedMatter.IsingModel.PressureBCIndep` |
| `Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean` | `PhyslibExt.CondensedMatter.IsingModel.PressureConvex` |
| `Atlas/StatisticalMechanics/Code/Ising/PressureFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.PressureSummary` |
| `Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean` | `PhyslibExt.CondensedMatter.IsingModel.PressureSurfaceVolume` |
| `Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.TailEventsErgodic` |
| `Atlas/StatisticalMechanics/Code/Ising/Transition.lean` | `PhyslibExt.CondensedMatter.IsingModel.Transition` |
| `Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.TransitionAssembly` |
| `Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean` | `PhyslibExt.CondensedMatter.IsingModel.TransitionFK` |
| `Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean` | `PhyslibExt.CondensedMatter.IsingModel.TransitionRegime` |
| `Atlas/StatisticalMechanics/Code/Ising/TransitionUncond.lean` | `PhyslibExt.CondensedMatter.IsingModel.TransitionPcLtOne` |
| `Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean` | `PhyslibExt.CondensedMatter.IsingModel.TwoReplica` |
| `Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean` | `PhyslibExt.CondensedMatter.IsingModel.TwoReplicaWeighted` |
| `Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BetacPc` |
| `Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Coloring` |
| `Atlas/StatisticalMechanics/Code/IsingFK/CorrelationMonotone.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.CorrelationMonotone` |
| `Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsInfinite` |
| `Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsLatticeBridge` |
| `Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsWired` |
| `Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.FvES` |
| `Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BoxMagnetization` |
| `Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.IsingBoxEncoding` |
| `Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagPercoIdBox` |
| `Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationCorrespondence` |
| `Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK` |
| `Atlas/StatisticalMechanics/Code/IsingFK/PcUpperAllDimensions.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions` |
| `Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls` |
| `Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean` | `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Q2` |
| `Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery` |
| `Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterContourBijection` |
| `Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.ContourCountInjection` |
| `Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.AnchoredBoundaryWalk` |
| `Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.ContourSubsetCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsAnchorEncode` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.DualCircuitDecoding` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.ComponentEulerCircuit` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsEulerParity` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsHoleFreeBoundary` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean` | `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit` |
| `Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.AugmentedTurnCancellation` |
| `Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.BlockCirculant` |
| `Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant2D.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.BlockCirculant2D` |
| `Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.EvenSubgraphCycles` |
| `Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalIntegrability` |
| `Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalPoint` |
| `Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalTransfer` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationCycleRemoval` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationCycleExponent` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleWeight.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationCycleWeight` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationCycles` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeClassification.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationEdgeClassification` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationEdgeComponent` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationEmbedding` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingDisjoint.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationEmbeddingDisjoint` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationEmbeddingTurns` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationExternalDeletion` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalToSpin` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationRepeatedEdge` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalCoefficient` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalEval` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalEvalAlgebra` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalMultiaffine` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalSeries` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSquarefree.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalSquarefree` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalSupport` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationInternalEndpoint` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationInternalMiddle` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationLoopClassification` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationLoopWalk` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationMiddleAffine` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationMiddleBalanced` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationMiddleCancellation` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationSpinGauge` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationSum` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationTransitionWalk` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationTransitionWeights` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationTurnTransfer` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkExtract` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkHomology` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkSign` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkTransition` |
| `Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWeighted` |
| `Atlas/StatisticalMechanics/Code/Onsager/DetLoopExpansion.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DetLoopExpansion` |
| `Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.DetWalkExp` |
| `Atlas/StatisticalMechanics/Code/Onsager/FinalAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.FreeEnergyOfSpinKacWard` |
| `Atlas/StatisticalMechanics/Code/Onsager/FirstReturnScale.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.FirstReturnScale` |
| `Atlas/StatisticalMechanics/Code/Onsager/FreeEnergy.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.FreeEnergy` |
| `Atlas/StatisticalMechanics/Code/Onsager/HighTemp.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.HighTemp` |
| `Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.IntegrandLimit` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWDetLimit` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWEdgeScale` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWFourier.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWFourier` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWLemma5.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWLemma5` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWLoopWeight.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWLoopWeight` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffine.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWMultiaffine` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffineBounded.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWMultiaffineBounded` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWPhaseLemma5` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWPhaseLoops` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWSpectral` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWSpinFourier` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeighted` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedBounds` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBuckets.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedBuckets` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedCancellation` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedDeletion.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedDeletion` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedHomology.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedHomology` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedLemma5` |
| `Atlas/StatisticalMechanics/Code/Onsager/KWZeroEdge.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.KWZeroEdge` |
| `Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.MvSeriesAnalyticUniqueness` |
| `Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.OnsagerFormula` |
| `Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.PeriodicTurnClosure` |
| `Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.Pressure` |
| `Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.RiemannPeriodic` |
| `Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic2D.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.RiemannPeriodic2D` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly1.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoopSplit` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoopReversal` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanDetFactor` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanBucketCancellation` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanConvergence` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFactor` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanGenericCancellation` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFirstReturnFactor` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanOrbitSum` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFirstReturn` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLemma5` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanListSeries` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanLoop.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoop` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanProductFormula` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanReroot` |
| `Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanSplit` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinKacWardResidue` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCharacter` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCoefficientInduction` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCoefficientTarget` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinPolynomial` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedAffine.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinWeightedAffine` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedBase.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinWeightedBase` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedRecurrence.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinWeightedRecurrence` |
| `Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinWeightedTarget` |
| `Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.StateWeightedDeletion` |
| `Atlas/StatisticalMechanics/Code/Onsager/SymbolDet.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.SymbolDet` |
| `Atlas/StatisticalMechanics/Code/Onsager/Torus.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusContractibleLoop` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusDecoration` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusIntersection` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusLoopCharacter` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusLoopHomology` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusPeriodicLift` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusPrimitiveWinding` |
| `Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusSpinSectors` |
| `Atlas/StatisticalMechanics/Code/Onsager/TracePowWalk.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TracePowWalk` |
| `Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TrivalentCycles` |
| `Atlas/StatisticalMechanics/Code/Onsager/TurnReversal.lean` | `PhyslibExt.CondensedMatter.IsingModel.Onsager.TurnReversal` |
| `Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneZeroOrOne` |
| `Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneErgodic` |
| `Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge` |
| `Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness` |
| `Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.PcUpperViaFK` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABClusterCondition` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABCouplingReindex` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABFieldDeriv` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABFiniteGraph` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABFiniteSymmetry` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABGhostInfluence` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABGhostRegularity` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABInequalities` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABPivotalFirstExit` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABInfiniteGhost` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABHypercubic` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABPhysicalDeriv` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABThermodynamicPassage` |
| `Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.AizenmanBarsky` |
| `Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABPivotalBounds` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BackboneProps` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BackboneDecomposition` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BcEqIsing` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaReparam` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BkCriterion` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BkFirstExit` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BkLattice` |
| `Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BkInhomogeneous` |
| `Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BoxMagnetizationRatio` |
| `Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BoxMagnetizationRatioLattice` |
| `Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ClusterLowerBound` |
| `Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MultigraphClusterSwitching` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentSplitting` |
| `Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ClusterFactorization` |
| `Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep` |
| `Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.DeltaBound` |
| `Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewrite.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.DeltaRewrite` |
| `Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.DeltaRewriteDichotomy` |
| `Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BoundaryErrorLimit` |
| `Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BoundaryErrorLattice` |
| `Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.FieldGhostDict` |
| `Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.EdgeCopyEncoding` |
| `Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyDischarge.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SwitchingGap` |
| `Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSConcavity` |
| `Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationFieldDeriv` |
| `Atlas/StatisticalMechanics/Code/Sharpness/GHSUnconditional.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSInequality` |
| `Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.GhostCurrentRep` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaDerivCurrent` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.HighTempPlusBox` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.HighTempSimon` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.HighTempSources` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.HighTempSwitching` |
| `Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.HighTempVertexField` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingExponentialPlus` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingMagnetizationZero.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingMagnetizationZero` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.AbstractSharpness` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SimonLiebSelfImprovement` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessUnconditional.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingSharpnessTheorem` |
| `Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingSusceptibilityPlus` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsing.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsing` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingFinite` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldLimit` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingIntegrated` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingMass` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingPlusBridge` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingState` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldPercoInhom` |
| `Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MultiReplica` |
| `Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercolationMeanfield` |
| `Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ConnWithinFactorization` |
| `Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent` |
| `Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBeta` |
| `Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Simon` |
| `Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SimonLieb` |
| `Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SimonPlusLimit` |
| `Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Switching` |
| `Atlas/StatisticalMechanics/Code/Sharpness/SwitchingCovariance.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SwitchingCovariance` |
| `Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SwitchingDichotomy` |
| `Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildeBc` |
| `Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.TwoReplica` |
| `Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.WeightedFieldGhost` |
| `Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxFreeEnergyBound` |
| `Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction` |
| `Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean` | `PhyslibExt.StatisticalMechanics.RandomCluster.BoxVanHoveLimit` |
| `Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationConcavity` |
| `Atlas/StatisticalMechanics/Code/Walls/gc_core.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSSignCondition` |
| `Atlas/StatisticalMechanics/Code/Walls/gc_ergrep.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRepZeroField` |
| `Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationSmooth` |
| `Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean` | `PhyslibExt.CondensedMatter.IsingModel.Sharpness.UrsellGap` |
| `Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean` | `PhyslibExt.CondensedMatter.IsingModel.EdgeRemovalSupermult` |

## MathlibExt (second round)

The second round ported the mathematics and computer science that the physics remainder depends
on, together with the modules they need. Duplicate and vacuous declarations were removed during the
port. Several ported modules state conditional results or record refutations; their module docs
say exactly what is proved.

| Source file | Module |
| --- | --- |
| `Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean` | `MathlibExt.Probability.Configuration.AeTailInvariant` |
| `Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean` | `MathlibExt.Dynamics.Ergodic.MaximalBirkhoff` |
| `Atlas/StatisticalMechanics/Code/Foundations/BirkhoffErgodic.lean` | `MathlibExt.Dynamics.Ergodic.BirkhoffErgodic` |
| `Atlas/StatisticalMechanics/Code/Foundations/EqualFiberHall.lean` | `MathlibExt.Combinatorics.Hall.EqualFiber` |
| `Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean` | `MathlibExt.Dynamics.Ergodic.ErgodicStructure` |
| `Atlas/StatisticalMechanics/Code/Foundations/FiniteBidegreeHall.lean` | `MathlibExt.Combinatorics.Hall.FiniteBidegree` |
| `Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean` | `MathlibExt.Analysis.Matrix.FiniteNonnegativeMatrixRate` |
| `Atlas/StatisticalMechanics/Code/Foundations/FractionalHall.lean` | `MathlibExt.Combinatorics.Hall.Fractional` |
| `Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean` | `MathlibExt.Probability.Configuration.TailSpecification` |
| `Atlas/StatisticalMechanics/Code/Foundations/WeightedFiniteInjection.lean` | `MathlibExt.Algebra.BigOperators.WeightedFiniteInjection` |
| `Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean` | `MathlibExt.Probability.CorrelationInequalities.BoxDownCompressionCounterexample` |
| `Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerOrbitSlab` |
| `Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerSwapInjection` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyCounterexample` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyMonoRefute` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerCompressionMarginals` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyDoubleCover` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricBoxCompression` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerWeightInjection` |
| `Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean` | `MathlibExt.Probability.CorrelationInequalities.ReimerOrbitCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle` |
| `Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingVisitsRows` |
| `Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit` |
| `Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite` |
| `Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite` |
| `Atlas/StatisticalMechanics/Code/Lattice/CollaredWalkCrossing.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CollaredWalkCrossing` |
| `Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner` |
| `Atlas/StatisticalMechanics/Code/Lattice/CycleLength.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleLength` |
| `Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction` |
| `Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExtremeCell` |
| `Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness` |
| `Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner` |
| `Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall` |
| `Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit` |
| `Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness` |
| `Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStep` |
| `Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStepCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialSurjectivity` |
| `Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialDartSetsJordan` |
| `Atlas/StatisticalMechanics/Code/Lattice/FiniteComplementConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FarLeftWalk` |
| `Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet` |
| `Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount` |
| `Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd` |
| `Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkInducedGraph` |
| `Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport` |
| `Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedProof.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton` |
| `Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.InteriorOrientation` |
| `Atlas/StatisticalMechanics/Code/Lattice/InteriorWindingClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FjordInteriorDisconnected` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingColumnArc` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportInterior` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSaturatedOrbitJordan` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanSeparationConditional` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitTailWindingWitness` |
| `Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RowArcSeparatingSet` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingDescentStepCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingFacts.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingFacts` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorDescent` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparation` |
| `Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.LeafInsertionCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.LeftFenceAnchor` |
| `Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.LexMinOrientation` |
| `Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorConnectivity` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates` |
| `Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingRevMatch` |
| `Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitSeparates` |
| `Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape` |
| `Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.BeaconFloodFill` |
| `Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportExteriorCovered` |
| `Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle` |
| `Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RayAlternation` |
| `Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.RowLinkedDescent` |
| `Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample` |
| `Atlas/StatisticalMechanics/Code/Lattice/StarHullFinite.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullFinite` |
| `Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullPeriod` |
| `Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut` |
| `Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullUmlaufsatz` |
| `Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullWinding` |
| `Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk` |
| `Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.TotalTurnFour` |
| `Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.NonCutSiteInsertion` |
| `Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases` |
| `Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzRotation` |
| `Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzEar` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingEarInduction` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitnessOfExterior` |
| `Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean` | `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitWinds` |
| `Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean` | `MathlibExt.Probability.OSSS.BetaCMatch` |
| `Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean` | `MathlibExt.Probability.OSSS.BetaThresholdBound` |
| `Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean` | `MathlibExt.Probability.OSSS.FKSharpDiffIneq` |
| `Atlas/StatisticalMechanics/Code/OSSS/Integration.lean` | `MathlibExt.Probability.OSSS.Integration` |
| `Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean` | `MathlibExt.Probability.OSSS.IntegrationSubcritical` |
| `Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean` | `MathlibExt.Probability.OSSS.IntegrationSubcriticalAssembly` |
| `Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean` | `MathlibExt.Probability.OSSS.Monotonic` |
| `Atlas/StatisticalMechanics/Code/OSSS/RevealmentSum.lean` | `MathlibExt.Probability.OSSS.RevealmentSum` |
| `Atlas/StatisticalMechanics/Code/OSSS/RussoPrefactor.lean` | `MathlibExt.Probability.OSSS.RussoPrefactor` |
| `Atlas/StatisticalMechanics/Code/OSSS/WiredDenominatorArithmetic.lean` | `MathlibExt.Probability.OSSS.WiredDenominatorArithmetic` |
| `Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean` | `MathlibExt.Probability.Percolation.DiscreteJordanSeparation` |
| `Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFalse.lean` | `MathlibExt.Probability.Percolation.DiscreteJordanSeparationFalse` |
| `Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean` | `MathlibExt.Probability.Percolation.DiscreteJordanSeparationVariant` |
| `Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean` | `MathlibExt.Probability.Percolation.FarDartContour` |
| `Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean` | `MathlibExt.Combinatorics.SimpleGraph.TreeTripod` |
| `Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean` | `MathlibExt.Probability.Percolation.OutermostContour` |
| `Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean` | `MathlibExt.Probability.Percolation.PcFarContour` |
| `Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean` | `MathlibExt.Probability.Percolation.RussoFormula` |
| `Atlas/StatisticalMechanics/Code/Percolation/TreeExteriorAmalgam.lean` | `MathlibExt.Combinatorics.SimpleGraph.TreeExteriorAmalgam` |
| `Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean` | `MathlibExt.Probability.Percolation.TreePercolation` |
| `Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreLower.lean` | `MathlibExt.Probability.OSSS.AdaptiveFibreLower` |
| `Atlas/StatisticalMechanics/Code/Probability/AdaptiveFibreStep.lean` | `MathlibExt.Probability.OSSS.AdaptiveFibreStep` |
| `Atlas/StatisticalMechanics/Code/Probability/BonamiVectorTwoPoint.lean` | `MathlibExt.Probability.Hypercontractivity.BonamiTensorStep` |
| `Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean` | `MathlibExt.Probability.CorrelationInequalities.ContinuousFKG` |
| `Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean` | `MathlibExt.Probability.CorrelationInequalities.ContinuousFKGAdapter` |
| `Atlas/StatisticalMechanics/Code/Probability/FiniteExponentialRateComparison.lean` | `MathlibExt.Probability.Hypercontractivity.FiniteExponentialRateComparison` |
| `Atlas/StatisticalMechanics/Code/Probability/FiniteWitnessInsertionIteration.lean` | `MathlibExt.Probability.Configuration.FiniteWitnessInsertionIteration` |
| `Atlas/StatisticalMechanics/Code/Probability/FiniteWitnessUnionBound.lean` | `MathlibExt.Probability.Configuration.FiniteWitnessUnionBound` |
| `Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean` | `MathlibExt.Probability.CorrelationInequalities.HolleyFKG` |
| `Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean` | `MathlibExt.Combinatorics.SimpleGraph.Menger.LinkageSeparator` |
| `Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean` | `MathlibExt.Combinatorics.SimpleGraph.Menger.MengerSplice` |
| `Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean` | `MathlibExt.Probability.Hypercontractivity.PBiasedHCLib` |
| `Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean` | `MathlibExt.Probability.Hypercontractivity.RhoOptimiseEngine` |
| `Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean` | `MathlibExt.Probability.StochasticOrder.StrassenFiniteCoupling` |
| `Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean` | `MathlibExt.Probability.Hypercontractivity.TwoPointLSI` |
| `Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean` | `MathlibExt.Probability.Percolation.RSW.BoxCrossing` |
| `Atlas/StatisticalMechanics/Code/RSW/BoxCrossingCapstone.lean` | `MathlibExt.Probability.Percolation.RSW.BoxCrossingCapstone` |
| `Atlas/StatisticalMechanics/Code/RSW/Continuity.lean` | `MathlibExt.Probability.Percolation.RSW.Continuity` |
| `Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean` | `MathlibExt.Probability.Percolation.RSW.ExpDecayUpgrade` |
| `Atlas/StatisticalMechanics/Code/RSW/OneArm.lean` | `MathlibExt.Probability.Percolation.RSW.OneArm` |
| `Atlas/StatisticalMechanics/Code/RSW/P4ImpliesP5.lean` | `MathlibExt.Probability.Percolation.RSW.P4ImpliesP5` |
| `Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean` | `MathlibExt.Probability.Percolation.RSW.P5Equivalences` |
| `Atlas/StatisticalMechanics/Code/RSW/Push.lean` | `MathlibExt.Probability.Percolation.RSW.Push` |
| `Atlas/StatisticalMechanics/Code/RSW/Renorm.lean` | `MathlibExt.Probability.Percolation.RSW.Renorm` |
| `Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean` | `MathlibExt.Probability.Percolation.RSW.SelfDuality` |
| `Atlas/StatisticalMechanics/Code/RSW/StripCases.lean` | `MathlibExt.Probability.Percolation.RSW.StripCases` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean` | `MathlibExt.Probability.BrownianMotion.BrownianCompactCylinderIntersection` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean` | `MathlibExt.Probability.BrownianMotion.BrownianContinuousModification` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean` | `MathlibExt.Probability.BrownianMotion.BrownianDyadicApproximation` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean` | `MathlibExt.Probability.BrownianMotion.BrownianDyadicControl` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicModulus.lean` | `MathlibExt.Probability.BrownianMotion.BrownianDyadicModulus` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean` | `MathlibExt.Probability.BrownianMotion.BrownianFiniteDimensional` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianKolmogorovTail.lean` | `MathlibExt.Probability.BrownianMotion.BrownianKolmogorovTail` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean` | `MathlibExt.Probability.BrownianMotion.BrownianModificationLaw` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean` | `MathlibExt.Probability.BrownianMotion.BrownianMomentBound` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean` | `MathlibExt.Probability.BrownianMotion.BrownianProductProcess` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean` | `MathlibExt.Probability.BrownianMotion.BrownianProjectiveContent` |
| `Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean` | `MathlibExt.Probability.BrownianMotion.BrownianProjectiveExtension` |
| `Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianLaw.lean` | `MathlibExt.Probability.BrownianMotion.CanonicalBrownianLaw` |
| `Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean` | `MathlibExt.Probability.BrownianMotion.CanonicalBrownianSLE` |
| `Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean` | `MathlibExt.Analysis.Complex.Loewner.CapacityNonneg` |
| `Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean` | `MathlibExt.Analysis.Complex.Loewner.CapacityProps` |
| `Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean` | `MathlibExt.Analysis.Complex.Loewner.ChainCapacity` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerCapacity` |
| `Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean` | `MathlibExt.Analysis.Complex.Loewner.LoewnerHolomorphicDependence` |
| `Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean` | `MathlibExt.Probability.BrownianMotion.StandardBrownianLaw` |
| `Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.Kesten` |
| `Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.KestenCrossingDecay` |
| `Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf` |
| `Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.SelfDualDichotomy` |
| `Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.SharpThreshold` |
| `Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.ZhangFourSides` |
| `Atlas/StatisticalMechanics/Code/TwoDim/ZhangLowerBound.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.ZhangLowerBound` |
| `Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean` | `MathlibExt.Probability.Percolation.TwoDimensional.ZhangRotSymmetry` |
| `Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean` | `MathlibExt.Probability.Percolation.Universality.BXPAllAspect` |
| `Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean` | `MathlibExt.Probability.Percolation.Universality.BXPFromRSW` |
| `Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean` | `MathlibExt.Probability.Percolation.Universality.BXPTransfer` |
| `Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoast` |
| `Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean` | `MathlibExt.Probability.Percolation.Universality.BoxCrossingDichotomy` |
| `Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean` | `MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples` |
| `Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingArc` |
| `Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor` |
| `Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingAnchor` |
| `Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean` | `MathlibExt.Probability.Percolation.Universality.CrossingReflection` |
| `Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean` | `MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance` |
| `Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean` | `MathlibExt.Probability.Percolation.Universality.DualCircuitToWalk` |
| `Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean` | `MathlibExt.Probability.Percolation.Universality.DualCutToPath` |
| `Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualDichotomy` |
| `Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean` | `MathlibExt.Probability.Percolation.Universality.FrameChangeIso` |
| `Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean` | `MathlibExt.Probability.Percolation.Universality.DualConfigLaw` |
| `Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean` | `MathlibExt.Probability.Percolation.Universality.LeftReachJordanSeparation` |
| `Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean` | `MathlibExt.Probability.Percolation.Universality.KestenAssembly` |
| `Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean` | `MathlibExt.Probability.Percolation.Universality.KestenHalf` |
| `Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingFrontier` |
| `Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean` | `MathlibExt.Probability.Percolation.Universality.PlanarDualCutConnected` |
| `Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossing` |
| `Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean` | `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoastAll` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean` | `MathlibExt.Probability.Percolation.Universality.RSWAspectInduction` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWBandBound.lean` | `MathlibExt.Probability.Percolation.Universality.RSWBandBound` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean` | `MathlibExt.Probability.Percolation.Universality.RSWBxpAssembly` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWConstantMaintenance.lean` | `MathlibExt.Probability.Percolation.Universality.RSWConstantMaintenance` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean` | `MathlibExt.Probability.Percolation.Universality.DualCrossingFrameCounterexample` |
| `Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean` | `MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick` |
| `Atlas/StatisticalMechanics/Code/Universality/STT.lean` | `MathlibExt.Probability.Percolation.Universality.STT` |
| `Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean` | `MathlibExt.Probability.Percolation.Universality.STTTransport` |

## Not ported

The following stays in `Atlas/StatisticalMechanics/Code` and outside the root build. Counts are
modules (`.lean` files) and lines (`wc -l`) at the time of the second round. Each module is
counted once, under the first category that applies in the order below. The tables below
account for 655 first-round rows and 202 second-round rows (one source,
`Code/Percolation/ClusterDualContour.lean`, is in both tables: removed in the first round, its
definition ported in the second), 1 deleted module, and the categories below: 655 + 202 - 1
(duplicate) + 1 (deleted) + 6,077 (categories) = 6,934 distinct source modules accounted for.
The earlier draft claimed 238 second-round rows
and 6,970 source modules in total; that did not reconcile with the tables, and the remaining
36-module gap is an open reconciliation item: do not treat the coverage as complete until the
missing 36 source modules are either added as rows or accounted for in the categories.

### Physics remainder (636 modules, 299,048 lines)

These are the modules that the physics results (random-cluster/FK, Ising, sharpness, Onsager,
Beffara–Duminil-Copin, and the physics-facing percolation, OSSS and wall modules) need, minus
everything ported. They are left for a `PhyslibExt` follow-up. Every module they import is either
ported (first or second round) or in this group, so the follow-up needs nothing from the categories
further down.

| Area | Modules | Lines |
| --- | ---: | ---: |
| `BeffaraDC` | 38 | 11,656 |
| `FK` | 183 | 97,030 |
| `FrontierA` | 3 | 583 |
| `Ising` | 4 | 3,202 |
| `OSSS` | 81 | 40,089 |
| `Onsager` | 1 | 293 |
| `Percolation` | 76 | 31,562 |
| `Probability` | 1 | 362 |
| `Sharpness` | 49 | 20,140 |
| `TwoDim` | 4 | 3,138 |
| `Universality` | 4 | 13,226 |
| `Walls` | 192 | 77,767 |

### `Check*` verification files (1,981 modules, 39,452 lines)

These are scratch files (`Check*.lean`) that state or `#check` a result to confirm that it
elaborates. They hold no reusable mathematics, and no ported module imports them.

### Frontier and exploratory directories (2,087 modules, 1,025,815 lines)

These are exploratory attempts on open or out-of-scope problems. No ported module and no module of
the physics remainder imports them. The counts exclude `Check*` files and the 3 `FrontierA` modules
that belong to the physics remainder.

| Directory | Modules | Lines |
| --- | ---: | ---: |
| `FrontierA` | 1124 | 388,661 |
| `FrontierB` | 114 | 37,779 |
| `FrontierC` | 1 | 490 |
| `FrontierD` | 738 | 256,394 |
| `Exact3D` | 110 | 342,491 |

### Unused scaffolding (1,034 modules, 507,152 lines)

These are intermediate steps and alternative routes that no ported module and no module of the
physics remainder imports.

| Directory | Modules | Lines |
| --- | ---: | ---: |
| `Universality` | 425 | 303,540 |
| `Walls` | 609 | 203,612 |

### Unused modules in the physics areas (339 modules, 129,039 lines)

These modules sit in physics directories but are imported by no ported module and no module of the
physics remainder. They are used only by `Check*` files, frontier files or each other, or by nothing
at all: superseded routes, conditional "close" files, and obstruction notes.

| Directory | Modules | Lines |
| --- | ---: | ---: |
| `BeffaraDC` | 4 | 2,131 |
| `FK` | 63 | 25,212 |
| `Ising` | 187 | 72,329 |
| `IsingFK` | 3 | 514 |
| `Lattice` | 2 | 976 |
| `OSSS` | 9 | 4,948 |
| `Onsager` | 59 | 19,540 |
| `RSW` | 3 | 973 |
| `SLE` | 5 | 1,115 |
| `Sharpness` | 4 | 1,301 |

### Ported, then deleted

- `Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean` (second round). Every declaration
  in its ported copy was a wrapper around Mathlib's `MeasureTheory.Measure.infinitePi` API with no
  users, so the declarations were deleted and the empty module was removed. Use Mathlib's
  `Measure.infinitePi` instead.
- First round: no ported module was deleted as a whole. Two pairs of source files were merged into
  one module each, and both sources of each pair appear in the first-round table:
  - `Code/FK/EdgeConfigZ.lean` and `Code/Walls/fkc_rqbulkfraction.lean` →
    `PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction`;
  - `Code/Ising/EvenSubgraphDecomp.lean` and `Code/Ising/KWClosedWalkParity.lean` →
    `PhyslibExt.CondensedMatter.IsingModel.KWClosedWalkParity`.
- Declarations deleted inside surviving modules (duplicates of Mathlib or of earlier ports, and
  declarations whose hypotheses were proved unsatisfiable) are listed in the pull-request
  descriptions, not here.
