/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveFamilyCovLower

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveFamilyCovLower`

All instances use the random-cluster mass `μ₂` on the complete graph on `Fin 2` at `p = 1/2`,
`q = 2`, the one-tree family `Unit → DecisionTree` given by the one-query tree on `s(0, 1)`,
and its function `f = evalR`.

* `bareAdaptiveFamilyOSSS_not_arbitrary`: the library's refutation of the bare family OSSS;
* non-vacuity of `AdaptiveFamilyOSSS` via `adaptiveFamilyOSSS_of_causal`;
* `var_le_avg_adaptive_reveal_mul_sum_cov_unconditional` with `D = 1`;
* `fk_q2_cov_lower_bound_of_adaptive_family_unconditional` with `R = 1`, `D = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveFamilyCovLower

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.FamilyEqzzzResolution
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.FrontierFamilyClose
open _root_.StatMech.OSSS.LindebergTree _root_.StatMech.OSSS.Monotonic

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- The one-query tree on `s(0, 1)`, returning the state of that edge. -/
local notation "T₁" => (DecisionTree.node s(0, 1) (DecisionTree.leaf true)
  (DecisionTree.leaf false) : DecisionTree (Sym2 (Fin 2)))

/-- The one-query tree computes a monotone function. -/
theorem queryEdge_evalR_monotone : Monotone (DecisionTree.evalR T₁) := by
  intro ω ω' h
  have h01 := h s(0, 1)
  by_cases hω : ω s(0, 1) <;> by_cases hω' : ω' s(0, 1) <;>
    simp_all [DecisionTree.evalR, DecisionTree.eval, Bool.le_iff_imp]

/-- `μ₂` satisfies the FKG lattice condition. -/
theorem mu2_fkg : FKGLatticeCondition μ₂ :=
  FK.fkProb_FKGLatticeCondition ⊤ (by norm_num) (by norm_num) (by norm_num)

/-- Every revealment under `μ₂` is at most `1`. -/
theorem mu2_reveal_le_one (T : DecisionTree (Sym2 (Fin 2))) (e : Sym2 (Fin 2)) :
    revealmentMu μ₂ T e ≤ 1 :=
  frf_revealmentMu_le_one (fun ω => (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω).le)
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) T e

-- The bare family OSSS fails for an arbitrary (non-monotonic) measure.
example : ¬ BareAdaptiveFamilyOSSS (μ := StepCov.Counterexample.muU)
    (fun _ : Unit => DecisionTree.leaf false) (Lindeberg.coord false) :=
  bareAdaptiveFamilyOSSS_not_arbitrary

-- Non-vacuity: the one-tree family satisfies `AdaptiveFamilyOSSS` under `μ₂`.
example : AdaptiveFamilyOSSS (μ := μ₂) (fun _ : Unit => T₁) (DecisionTree.evalR T₁) :=
  adaptiveFamilyOSSS_of_causal (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) mu2_fkg _
    queryEdge_evalR_monotone (fun _ => rfl)

-- `Var f ≤ ∑ Cov` for the one-tree family (`D = 1`).
example : Lindeberg.var μ₂ (DecisionTree.evalR T₁) ≤
    1 * ∑ e, Lindeberg.cov μ₂ (DecisionTree.evalR T₁) (Lindeberg.coord e) :=
  var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) mu2_fkg
    (fun _ : Unit => T₁) queryEdge_evalR_monotone (fun _ => rfl) 1
    (fun e => by simpa using mu2_reveal_le_one T₁ e)

-- `θ (1 - θ) ≤ ∑ Cov` for the one-tree family (`R = 1`, `D = 1`).
example : Lindeberg.mean μ₂ (DecisionTree.evalR T₁) *
      (1 - Lindeberg.mean μ₂ (DecisionTree.evalR T₁)) / 1 ≤
    ∑ e, Lindeberg.cov μ₂ (DecisionTree.evalR T₁) (Lindeberg.coord e) :=
  fk_q2_cov_lower_bound_of_adaptive_family_unconditional ⊤ (by norm_num) (by norm_num)
    (fun _ : Unit => T₁) queryEdge_evalR_monotone
    (fun ω => by unfold DecisionTree.evalR; split_ifs <;> norm_num) (fun _ => rfl)
    (fun _ _ => 1) 1 one_pos (fun _ e => mu2_reveal_le_one T₁ e) (fun _ => by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveFamilyCovLower
