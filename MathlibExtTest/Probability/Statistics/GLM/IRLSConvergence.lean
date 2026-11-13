/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.GLM.IRLSConvergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Filter Metric Set Topology
open MathlibExt.Probability.Statistics.GLM.IRLSConvergence

/-! ### Boundary cases computed from the definitions -/

-- The constant `L / 2` in `norm_sub_sub_fderiv_le` is sharp: for `U x = x²` (`H x = 2 x`,
-- `L = 2`), the remainder between `0` and `1` equals `L / 2 * ‖1 - 0‖² = 1`.
example :
    ‖(1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - (2 * (0 : ℝ)) * (1 - 0)‖ = 2 / 2 * ‖(1 : ℝ) - 0‖ ^ 2 := by
  norm_num

-- The Lipschitz-derivative bound itself, instantiated at that sharp case.
private theorem smul_id_sub_smul_id (a c : ℝ) :
    a • ContinuousLinearMap.id ℝ ℝ - c • ContinuousLinearMap.id ℝ ℝ =
      (a - c) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp

private theorem norm_smul_id_le (a : ℝ) : ‖a • ContinuousLinearMap.id ℝ ℝ‖ ≤ ‖a‖ := by
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le

example :
    ‖(1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - ((2 * (0 : ℝ)) • ContinuousLinearMap.id ℝ ℝ) (1 - 0)‖ ≤
      2 / 2 * ‖(1 : ℝ) - 0‖ ^ 2 := by
  refine norm_sub_sub_fderiv_le (U := fun x : ℝ => x ^ 2)
    (H := fun x : ℝ => (2 * x) • ContinuousLinearMap.id ℝ ℝ) (s := univ) convex_univ
    (fun z _ => ?_) (fun z _ => ?_) (mem_univ _) (mem_univ _)
  · convert (hasDerivAt_pow 2 z).hasFDerivAt using 1
    ext
    simp
  · rw [smul_id_sub_smul_id, ← mul_sub]
    refine (norm_smul_id_le _).trans ?_
    rw [norm_mul]
    norm_num

-- The perturbation bound needs `M δ ≤ 1/2`: with `A₀ = id`, `A = 0`, `M = δ = 1`, the
-- conclusion `‖v‖ ≤ 2 M ‖A v‖` fails at `v = 1`.
example : ¬ (‖(1 : ℝ)‖ ≤ 2 * 1 * ‖(0 : ℝ →L[ℝ] ℝ) 1‖) := by
  simp

/-! ### Gaussian linear model: Fisher scoring reaches the root in one step

For the normal family with identity (canonical) link and one observation `y` with covariate `a`,
the score is `U β = a (y - a β)` and the Fisher information is `I β = a²`, constant, so `L = 0`. -/

-- The Fisher-scoring step `T β = β + U β / a² = y / a` lands on the root, from any start.
example (a y β : ℝ) (ha : a ≠ 0) : β + a * (y - a * β) / a ^ 2 = y / a := by
  field_simp
  ring

-- The root is `y / a`, computed from the score.
example (a y : ℝ) (ha : a ≠ 0) : a * (y - a * (y / a)) = 0 := by
  field_simp
  ring

/-! ### A nonlinear score: `U β = -β - β² / 2`, `I β = β + 1`

`I` is `1`-Lipschitz, `I 0 = 1`, the root is `0`, and the Fisher-scoring map is
`T β = β² / (2 (β + 1))`. -/

/-- The information `β ↦ (β + 1) • id`. -/
private noncomputable abbrev infoEx (β : ℝ) : ℝ →L[ℝ] ℝ := (β + 1) • ContinuousLinearMap.id ℝ ℝ

/-- The score `β ↦ -β - β² / 2`. -/
private noncomputable abbrev scoreEx (β : ℝ) : ℝ := -β - β ^ 2 / 2

/-- The Fisher-scoring map `β ↦ β² / (2 (β + 1))`. -/
private noncomputable abbrev stepEx (β : ℝ) : ℝ := β ^ 2 / (2 * (β + 1))

-- The scoring map solves `I β (T β - β) = U β` away from `β = -1`, computed from definitions.
example (β : ℝ) (hβ : β + 1 ≠ 0) : infoEx β (stepEx β - β) = scoreEx β := by
  simp only [infoEx, stepEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  field_simp
  ring

-- Quadratic error decay, computed from definitions: one step from `1/4` gives `1/40`.
example : stepEx (1 / 4) = 1 / 40 := by
  norm_num [stepEx]

-- At `β = -1` the information vanishes and the scoring equation has no solution, so some
-- radius restriction (`2 M L ε ≤ 1`, here `ε ≤ 1/2`) is needed.
example : ¬ ∃ t : ℝ, infoEx (-1) (t - (-1)) = scoreEx (-1) := by
  rintro ⟨t, ht⟩
  simp only [infoEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul] at ht
  norm_num at ht

/-! ### Non-vacuity: the hypotheses of the main theorems are satisfiable -/

private theorem hasFDerivAt_scoreEx (x : ℝ) : HasFDerivAt scoreEx (-infoEx x) x := by
  have h : HasDerivAt scoreEx (-1 - x) x := by
    have h' := ((hasDerivAt_id x).neg).sub ((hasDerivAt_pow 2 x).div_const 2)
    convert h' using 1
    · funext t
      simp [scoreEx, sub_eq_add_neg]
    · norm_num
  convert h.hasFDerivAt using 1
  ext
  simp
  ring

private theorem infoEx_lipschitz (x y : ℝ) : ‖infoEx x - infoEx y‖ ≤ 1 * ‖x - y‖ := by
  rw [infoEx, infoEx, smul_id_sub_smul_id, add_sub_add_right_eq_sub, one_mul]
  exact norm_smul_id_le _

private theorem stepEx_spec (x : ℝ) (hx : x ∈ ball (0 : ℝ) (1 / 2)) :
    infoEx x (stepEx x - x) = scoreEx x := by
  have hx' : -(1 / 2 : ℝ) < x := by
    rw [mem_ball, Real.dist_eq, sub_zero] at hx
    linarith [neg_abs_le x]
  have hne : x + 1 ≠ 0 := by linarith
  simp only [infoEx, stepEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  field_simp
  ring

-- Fisher scoring converges to the root `0` from every start in `ball 0 (1/2)`, with the
-- quadratic bound `‖Tⁿ⁺¹ β₀‖ ≤ ‖Tⁿ β₀‖²` (`M = L = 1`).
example (β₀ : ℝ) (hβ₀ : β₀ ∈ ball (0 : ℝ) (1 / 2)) :
    (∀ n, ‖stepEx^[n + 1] β₀ - 0‖ ≤ 1 * 1 * ‖stepEx^[n] β₀ - 0‖ ^ 2) ∧
      Tendsto (fun n => stepEx^[n] β₀) atTop (𝓝 0) := by
  have h := fisherScoring_local_convergence (U := scoreEx) (I := infoEx)
    (I₀inv := ContinuousLinearMap.id ℝ ℝ) (r := 1 / 2) (M := 1) (L := 1)
    (by norm_num [scoreEx]) (fun x _ => hasFDerivAt_scoreEx x)
    (fun x _ y _ => infoEx_lipschitz x y) (fun v => by simp [infoEx])
    ContinuousLinearMap.norm_id_le stepEx_spec le_rfl (by norm_num) hβ₀
  exact ⟨h.2.1, h.2.2.2⟩

-- The root `0` is the only score zero in `ball 0 (1/2)`; the other zero `-2` lies outside.
example : scoreEx (-2) = 0 ∧ (-2 : ℝ) ∉ ball (0 : ℝ) (1 / 2) := by
  constructor
  · norm_num [scoreEx]
  · rw [mem_ball, Real.dist_eq]
    norm_num

example (β : ℝ) (hβ : β ∈ ball (0 : ℝ) (1 / 2)) (h0 : scoreEx β = 0) : β = 0 :=
  eq_of_score_eq_zero (U := scoreEx) (H := fun x => -infoEx x)
    (H₀inv := -ContinuousLinearMap.id ℝ ℝ) (r := 1 / 2) (M := 1) (L := 1)
    (by norm_num [scoreEx]) (fun x _ => hasFDerivAt_scoreEx x)
    (fun x _ y _ => by rw [← neg_sub', norm_neg]; exact infoEx_lipschitz x y)
    (fun v => by simp [infoEx]) (by simp) le_rfl
    (by norm_num) hβ h0

-- In finite dimension a Newton map exists on the ball without being supplied.
example : ∃ T : ℝ → ℝ, ∀ x ∈ ball (0 : ℝ) (1 / 2),
    (fun x => -infoEx x) x (T x - x) = -scoreEx x :=
  exists_newton_map (H := fun x => -infoEx x) (H₀inv := -ContinuousLinearMap.id ℝ ℝ)
    (r := 1 / 2) (M := 1) (L := 1)
    (fun x _ y _ => by rw [← neg_sub', norm_neg]; exact infoEx_lipschitz x y)
    (fun v => by simp [infoEx]) (by simp) le_rfl
    (by norm_num)

#print axioms newton_local_convergence
#print axioms fisherScoring_local_convergence
#print axioms exists_newton_map
#print axioms eq_of_score_eq_zero
#print axioms norm_sub_sub_fderiv_le
#print axioms newton_step_error_le
