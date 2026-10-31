/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxConnect

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxConnect`

* `bc99_boxReachesNbr_fails`: the reach condition fails in `ℤ²` for `n = 3` (refutation).
* The last conjunct of `bc99_status`: in the three-ray configuration the cluster condition
  `bc56_ClusterReachesNbr` holds at `(1, 0)` (instance).
* `bc99_texBoxAttach_of_reachesNbr` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxConnect

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The box reach condition fails in `ℤ²` for `n = 3`.
example : ¬ bc56_BoxClusterReachesNbr 2 3 :=
  bc99_boxReachesNbr_fails

-- The cluster condition holds at `(1, 0)` in the three-ray configuration.
example : bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) :=
  bc99_status.2.2.2

-- The reach condition gives box attachment data.
example (n : ℕ) (h : bc56_BoxClusterReachesNbr 2 n) : tex_BoxAttachData 2 n :=
  bc99_texBoxAttach_of_reachesNbr h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxConnect
