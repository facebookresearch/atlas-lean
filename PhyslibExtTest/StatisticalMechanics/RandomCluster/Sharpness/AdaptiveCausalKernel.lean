/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalKernel

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalKernel`

All checks use the random-cluster mass on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`,
and the observable "edge `s(0, 1)` is open" (proved monotone below).

* `tripleCube_causal_integral_eq_crossTripleJointProb` for the triple order extending the
  one-query decision tree on `s(0, 1)`;
* `tripleCube_product_le_pairedCube_product` for the open-edge observable;
* `causal_fkg_cross_fiber` for the open-edge observable and the realized orders;
* `decisionTree_branch_adapt_step_fiber_le` at step `t = 1` of the one-query tree.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalKernel

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK MeasureTheory

/-- The open-edge indicator of `s(0, 1)` is monotone. -/
theorem openEdge_monotone :
    Monotone (fun ω : ConfigSpace (Sym2 (Fin 2)) => if ω s(0, 1) then (1 : ℝ) else 0) := by
  intro ω ω' h
  have h01 := h s(0, 1)
  by_cases hω : ω s(0, 1) <;> by_cases hω' : ω' s(0, 1) <;> simp_all [Bool.le_iff_imp]

/-- The open-edge indicator of `s(0, 1)` is bounded by `1`. -/
theorem openEdge_abs_le (ω : ConfigSpace (Sym2 (Fin 2))) :
    |(if ω s(0, 1) then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> norm_num

-- Exact law of the triple coupling for the tree querying `s(0, 1)`.
example (base seed : ConfigSpace (Sym2 (Fin 2)))
    (g : ConfigSpace (Sym2 (Fin 2)) → ConfigSpace (Sym2 (Fin 2)) → ℝ) :=
  tripleCube_causal_integral_eq_crossTripleJointProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) seed
      Finset.univ) base g

-- The triple coupling is dominated by the paired coupling for the open-edge observable.
example (base seed : ConfigSpace (Sym2 (Fin 2))) :=
  tripleCube_product_le_pairedCube_product
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num))
    (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) seed
      Finset.univ) base openEdge_monotone openEdge_abs_le openEdge_monotone openEdge_abs_le

-- FKG on a fiber of the causal coupling, for the open-edge observable.
example (base : ConfigSpace (Sym2 (Fin 2))) (σ : Fin (Fintype.card (Sym2 (Fin 2))) ≃ Sym2 (Fin 2))
    (U : Fin (Fintype.card (Sym2 (Fin 2))) → ℝ) :=
  causal_fkg_cross_fiber (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num))
    (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) base Finset.univ)
    (extendDecisionTree (.leaf true) base Finset.univ) base σ openEdge_monotone openEdge_abs_le
    s(0, 1) U

-- The adaptive step bound at step `1` of the one-query tree.
example (base : ConfigSpace (Sym2 (Fin 2))) (U : Fin (Fintype.card (Sym2 (Fin 2))) → ℝ) :=
  decisionTree_branch_adapt_step_fiber_le
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num))
    (.node s(0, 1) (.leaf true) (.leaf false)) base openEdge_monotone openEdge_abs_le 1 le_rfl
    (by simp [DecisionTree.queried]) Fintype.card_pos U

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalKernel
