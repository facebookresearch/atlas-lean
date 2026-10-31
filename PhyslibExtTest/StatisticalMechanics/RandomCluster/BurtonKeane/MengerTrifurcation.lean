/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerTrifurcation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerTrifurcation`

* `bc21_threeRay_trif_at_origin`: the three-ray configuration of `ℤ²` has a canonical
  trifurcation at the origin (instance).
* `bc21_originBranchSurvivalCut_of_canonicalTrifurcation` and
  `bc21_mengerCore_of_canonicalTrifurcation` applied to it (instance).
* `bc21_mengerCore_nonvacuous`: some configuration has a Menger core.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerTrifurcation

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.Percolation.DisjointPaths _root_.StatMech.Percolation.CtcWitness

-- The three-ray configuration has a canonical trifurcation at the origin.
example : IsCanonicalTrifurcation 2 threeRayConfig 0 :=
  bc21_threeRay_trif_at_origin

-- Its branches survive the removal of the origin.
example : bc21_OriginBranchSurvivalCut 2 threeRayConfig :=
  bc21_originBranchSurvivalCut_of_canonicalTrifurcation _ bc21_threeRay_trif_at_origin

-- It has a Menger core.
example : MengerCore threeRayConfig :=
  bc21_mengerCore_of_canonicalTrifurcation _ bc21_threeRay_trif_at_origin

-- Some configuration of `ℤ²` has a Menger core.
example : ∃ ω : ConfigSpace (Sym2 (Site 2)), MengerCore ω :=
  bc21_mengerCore_nonvacuous

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerTrifurcation
