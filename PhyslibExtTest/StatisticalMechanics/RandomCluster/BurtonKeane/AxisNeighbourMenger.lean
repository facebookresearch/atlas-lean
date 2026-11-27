/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisNeighbourMenger

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisNeighbourMenger`

* `bc56_threeRayConfig_reachesNbr_witness`: three explicit clusters reach origin neighbours;
* the off-axis line: `bc56_offAxisLine_cluster_infinite` and
  `bc56_offAxisLine_no_runsAlongAxis` (an infinite cluster that does not run along an axis);
* `bc56_boxMengerAttachment_of_reachesNbr` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AxisNeighbourMenger

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Three clusters of the three-ray configuration reach neighbours of the origin.
example : bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) :=
  bc56_threeRayConfig_reachesNbr_witness.1

-- The off-axis line has an infinite cluster that runs along no axis.
example : (cluster 2 bc56_offAxisLine (bc56_lp 0)).Infinite := bc56_offAxisLine_cluster_infinite
example : ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) 0 :=
  bc56_offAxisLine_no_runsAlongAxis 0

-- Reaching neighbours in every box gives the Menger attachment.
example {d n : ℕ} (h : bc56_BoxClusterReachesNbr d n) : bmm_BoxMengerAttachment d n :=
  bc56_boxMengerAttachment_of_reachesNbr h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AxisNeighbourMenger
