/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.ScalarParabolicComparison

/-!
# Tests for scalar parabolic nonnegativity

Checked consumers of the comparison theorems:

- a constant nonnegative profile with constant reaction and the matching
  source `K * a`;
- the steady linear profile `c t x = x`, whose spatial derivative is `1`
  and whose second spatial derivative is `0`;
- the bounded-state-box corollary on the constant profile `1` with zero
  reaction;
- numeric mass-action fixture values and the square-root invalid example.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.ScalarParabolicComparison

/-- Constant profile: `c = a ≥ 0`, `k = K ≥ 0` and `s = K * a` satisfy
`c_t - D * c_xx + k * c = s`, so the conclusion is `0 ≤ a` at every point
of the cylinder. -/
example {D L T K a : ℝ} (hD : 0 < D) (hL : 0 < L) (hT : 0 < T)
    (hK : 0 ≤ K) (ha : 0 ≤ a) {t x : ℝ}
    (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) : 0 ≤ a := by
  exact parabolic_solution_nonneg hD hL hT
    (c := fun _ _ => a) (ct := fun _ _ => 0) (cx := fun _ _ => 0)
    (cxx := fun _ _ => 0) (k := fun _ _ => K) (s := fun _ _ => K * a)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (by simpa using continuousOn_const)
    (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => hK)
    (fun _ _ _ _ => mul_nonneg hK ha)
    (fun _ _ => ha) (fun _ _ => ha) (fun _ _ => ha) ht hx

/-- Steady linear profile: `c t x = x` solves `c_t - D * c_xx = 0`, with
nonnegative initial data `x` on `[0, L]` and boundary values `0` and `L`;
the conclusion recovers `0 ≤ x` on the cylinder. -/
example {D L T : ℝ} (hD : 0 < D) (hL : 0 < L) (hT : 0 < T)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) : 0 ≤ x := by
  exact parabolic_solution_nonneg hD hL hT
    (c := fun _ y => y) (ct := fun _ _ => 0) (cx := fun _ _ => 1)
    (cxx := fun _ _ => 0) (k := fun _ _ => 0) (s := fun _ _ => 0)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_id' _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    continuousOn_snd
    (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => le_refl 0)
    (fun _ _ _ _ => le_refl 0)
    (fun y hy => hy.1) (fun _ _ => le_refl 0) (fun _ _ => hL.le) ht hx

/-- Bounded-box corollary on the constant profile `c = 1` with zero
reaction: every hypothesis is discharged directly. -/
example {t x : ℝ} (ht : t ∈ Set.Icc 0 1) (hx : x ∈ Set.Icc 0 1) :
    (0 : ℝ) ≤ 1 := by
  exact parabolic_solution_nonneg_of_lipschitzOn (D := 1) (L := 1) (T := 1)
    (M := 1) (K := 0)
    (c := fun _ _ => 1) (ct := fun _ _ => 0) (cx := fun _ _ => 0)
    (cxx := fun _ _ => 0) (r := fun _ _ _ => 0)
    (by norm_num)
    (fun _ _ _ _ => (hasDerivAt_const _ _).hasDerivWithinAt)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (by simpa using continuousOn_const)
    (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => by norm_num)
    (fun _ _ _ _ => (LipschitzWith.const (0 : ℝ)).lipschitzOnWith)
    (fun _ _ _ _ => le_refl 0)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    ht hx

/-- Mass-action fixture at `a = 1`, `b = 2`, `M = 1`, `u = -1`. -/
example : (2 * 1) * (-1 : ℝ) ≤ 1 - 2 * (-1 : ℝ) ^ 2 :=
  massAction_oneSided (by norm_num) (by norm_num) ⟨le_refl _, by norm_num⟩

example : LipschitzOnWith (Real.toNNReal (2 * 2 * 1))
    (fun u : ℝ => 1 - 2 * u ^ 2) (Set.Icc (-1) 0) :=
  massAction_lipschitzOn (by norm_num) (by norm_num)

/-- The square-root invalid example at `t = 2`: the profile solves the ODE
and is already negative, and no one-sided bound holds on `[-1, 0]`. -/
example : HasDerivAt (fun τ : ℝ => -τ ^ 2 / 4)
    (-Real.sqrt |(-(2 : ℝ) ^ 2 / 4)|) 2 :=
  sqrtReaction_solution (by norm_num)

example : (-(2 : ℝ) ^ 2 / 4) < 0 ∧
    ∃ u ∈ Set.Icc (-1) 0, -Real.sqrt |u| < (0 : ℝ) * u :=
  ⟨sqrtReaction_negative (by norm_num), sqrtReaction_not_oneSided 0 (by norm_num)⟩

end MathlibExt.Analysis.PDE.ScalarParabolicComparison
