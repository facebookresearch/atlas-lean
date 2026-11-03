/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveTau

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveTau`

All checks use the random-cluster mass `μ₂` on the complete graph on `Fin 2` at `p = 1/2`,
`q = 2`.

* non-vacuity of `StepCovBoundTwo`: it holds for every leaf tree;
* `fk_q2_osss_sharp` for a leaf tree, with the step bound discharged by that witness;
* `tree_osss` for the one-query tree on `s(0, 1)`, conditional on `StepCovBoundTwo`;
* `step_fiber_le` at step `t = 1` for the open-edge observable of `s(0, 1)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveTau

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveTau
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.StepCov
open _root_.StatMech.OSSS.LindebergTree

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- Non-vacuity: `StepCovBoundTwo` holds for a leaf tree (it reveals nothing). -/
theorem stepCovBoundTwo_leaf {E : Type*} [Fintype E] [DecidableEq E]
    (μ : ConfigSpace E → ℝ) (b : Bool) (f : ConfigSpace E → ℝ) :
    StepCovBoundTwo μ (.leaf b) f := by
  intro t e
  simp [freshAt, Lindeberg.mean]

/-- The open-edge indicator of `s(0, 1)` is monotone. -/
theorem openEdge_monotone :
    Monotone (fun ω : ConfigSpace (Sym2 (Fin 2)) => if ω s(0, 1) then (1 : ℝ) else 0) := by
  intro ω ω' h
  have h01 := h s(0, 1)
  by_cases hω : ω s(0, 1) <;> by_cases hω' : ω' s(0, 1) <;> simp_all [Bool.le_iff_imp]

-- Decision-tree OSSS on `K₂` for a leaf tree.
example (b : Bool) :
    Lindeberg.var μ₂ (DecisionTree.evalR (.leaf b)) ≤
      ∑ e, revealmentMu μ₂ (.leaf b) e *
        Lindeberg.cov μ₂ (DecisionTree.evalR (.leaf b)) (Lindeberg.coord e) :=
  fk_q2_osss_sharp ⊤ (by norm_num) (by norm_num) _ (stepCovBoundTwo_leaf _ b _)

-- Decision-tree OSSS for the one-query tree, conditional on the step bound.
example (hStep : StepCovBoundTwo μ₂ (.node s(0, 1) (.leaf true) (.leaf false))
      (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false)))) :
    Lindeberg.var μ₂ (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false))) ≤
      ∑ e, revealmentMu μ₂ (.node s(0, 1) (.leaf true) (.leaf false)) e *
        Lindeberg.cov μ₂ (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false)))
          (Lindeberg.coord e) :=
  tree_osss (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) _ hStep

-- The step bound on a fiber at `t = 1`, for the open-edge observable on `K₂`.
example {n : ℕ} (σ : Fin (n + 1) ≃ Sym2 (Fin 2)) (U : Fin (n + 1) → ℝ) :=
  step_fiber_le (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num)) σ openEdge_monotone
    (fun ω => by split_ifs <;> norm_num : ∀ ω : ConfigSpace (Sym2 (Fin 2)),
      |(if ω s(0, 1) then (1 : ℝ) else 0)| ≤ 1) 1 le_rfl (Nat.succ_pos n) U

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveTau
