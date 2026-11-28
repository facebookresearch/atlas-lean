/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerOriginRoute

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerOriginRoute`

* `bc20_hardDir_boxGraph`: Menger's hard direction holds in the box graph of the all-closed
  configuration of `ℤ²` (instance), applied with `k = 0`.
* `bc20_originBox` is the origin.
* `bc20_originBranchSurvival_of_originFree` and `bc20_mengerCore_of_originBranchSurvival` as
  conditional statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerOriginRoute

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.Percolation.DisjointPaths

-- The hard direction in the box graph gives an (empty) family for `k = 0`.
example : Nonempty (bc16_DisjointPathFamily (bc20_boxGraph 2 1 fun _ => false)
    (bc20_boundaryV 2 1) {bc20_originBox 2 1} (Fin 0)) :=
  bc20_hardDir_boxGraph 2 1 _ _ _ 0 fun _ _ => Nat.zero_le _

-- The distinguished box vertex is the origin.
example : (bc20_originBox 2 3 : Site 2) = 0 := rfl

-- Origin-free clusters give origin branch survival, hence the Menger core.
example (ω : ConfigSpace (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hdist : cluster 2 ω a₁ ≠ cluster 2 ω a₂ ∧ cluster 2 ω a₁ ≠ cluster 2 ω a₃ ∧
      cluster 2 ω a₂ ≠ cluster 2 ω a₃)
    (h0 : (0 : Site 2) ∉ cluster 2 ω a₁ ∧ (0 : Site 2) ∉ cluster 2 ω a₂ ∧
      (0 : Site 2) ∉ cluster 2 ω a₃)
    (hinf : (cluster 2 ω a₁).Infinite ∧ (cluster 2 ω a₂).Infinite ∧ (cluster 2 ω a₃).Infinite) :
    MengerCore ω :=
  bc20_mengerCore_of_originBranchSurvival 2 ω
    (bc20_originBranchSurvival_of_originFree 2 ω a₁ a₂ a₃ hne hadj hdist h0 hinf)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerOriginRoute
