/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteVolumeCutCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteVolumeCutCount`

In the plane, on the upper-lines configuration at `L = 3`:
* `bc86_coarseTrif_is_branchpoint` and `bc86_singleBox_cut_free_of_le_one` applied to its coarse
  trifurcation at the origin;
* `bc86_status`: the upper lines have `N = ⊤`;
* `bc86_finiteN_ae` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteVolumeCutCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The upper lines are a coarse trifurcation at the origin for `L = 3`. -/
theorem ul_trif : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines le_rfl

-- Three infinite, pairwise disconnected arms after removing the box.
example : ∃ a₁ a₂ a₃ : Site 2,
    (cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁).Infinite ∧
    (cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂).Infinite ∧
    (cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₃).Infinite ∧
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₂ ∧
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₃ ∧
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂ a₃ :=
  bc86_coarseTrif_is_branchpoint _ 3 ul_trif

-- The arms are pairwise unreachable in the contracted lattice.
example : ∃ a₁ a₂ a₃ : Site 2,
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₂ ∧
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₃ ∧
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₂ a₃ :=
  bc86_singleBox_cut_free_of_le_one _ 3 ul_trif

-- The upper lines have `N = ⊤`.
example : numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc86_status.2.2.2.2

-- Almost-sure fibre data and the coarse step give finite `N` almost surely.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hgn : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin 2 → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c)
    (hexist : bc61_CoarseTrifExistence μ L) : μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 :=
  bc86_finiteN_ae μ (by norm_num) L hinv hgn hexist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteVolumeCutCount
