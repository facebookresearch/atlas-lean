/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The BFGS quasi-Newton update

A quasi-Newton method replaces the Hessian by an approximation `B` updated from the step
`s = x⁺ - x` and the gradient change `y = ∇f(x⁺) - ∇f(x)` so that the *secant equation*
`B⁺ s = y` holds. The BFGS update (Broyden, Fletcher, Goldfarb and Shanno, 1970) is

`B⁺ = B - (B s)(B s)ᵀ / ⟪B s, s⟫ + y yᵀ / ⟪y, s⟫`

(J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear
Equations*, Prentice-Hall 1983, Section 9.2). This file proves that it satisfies the secant
equation, preserves symmetry, and preserves positive definiteness exactly when the curvature
condition `⟪y, s⟫ > 0` holds (the condition under which, as stated in Dennis and Schnabel's
Section 9.2, a positive definite secant update exists).
-/

@[expose] public section

namespace MathlibExt.Analysis.Optimization.QuasiNewton

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **BFGS update.** For a Hessian approximation `B`, a step `s` and a gradient change `y`,
`B⁺ v = B v - (⟪B s, v⟫ / ⟪B s, s⟫) • B s + (⟪y, v⟫ / ⟪y, s⟫) • y`, i.e.
`B⁺ = B - (B s)(B s)ᵀ / (sᵀ B s) + y yᵀ / (yᵀ s)` (Dennis and Schnabel 1983, Section 9.2). -/
noncomputable def bfgsUpdate (B : E →L[ℝ] E) (s y : E) : E →L[ℝ] E :=
  B - (1 / ⟪B s, s⟫) • (innerSL ℝ (B s)).smulRight (B s) +
    (1 / ⟪y, s⟫) • (innerSL ℝ y).smulRight y

theorem bfgsUpdate_apply (B : E →L[ℝ] E) (s y v : E) :
    bfgsUpdate B s y v = B v - (⟪B s, v⟫ / ⟪B s, s⟫) • B s + (⟪y, v⟫ / ⟪y, s⟫) • y := by
  simp only [bfgsUpdate, add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_smul, one_div_mul_eq_div]

/-- **The BFGS update satisfies the secant equation.** If `⟪B s, s⟫ ≠ 0` and `⟪y, s⟫ ≠ 0`, then
`B⁺ s = y` (Dennis and Schnabel 1983, Section 9.2: the BFGS update "obeys `H₊ s_c = y_c`"). -/
theorem bfgsUpdate_apply_self {B : E →L[ℝ] E} {s y : E} (hB : ⟪B s, s⟫ ≠ 0) (hy : ⟪y, s⟫ ≠ 0) :
    bfgsUpdate B s y s = y := by
  rw [bfgsUpdate_apply, div_self hB, div_self hy, one_smul, one_smul, sub_self, zero_add]

/-- **The BFGS update preserves symmetry.** If `B` is symmetric, so is `B⁺` (Dennis and Schnabel
1983, Section 9.2: `H₊ - H_c` is a symmetric matrix of rank at most two). -/
theorem bfgsUpdate_symm {B : E →L[ℝ] E} (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (s y : E) :
    ∀ u v, ⟪bfgsUpdate B s y u, v⟫ = ⟪u, bfgsUpdate B s y v⟫ := by
  intro u v
  simp only [bfgsUpdate_apply, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hsymm u v]
  rw [real_inner_comm (B s) u, real_inner_comm y u]
  ring

/-- The `B`-Cauchy–Schwarz identity behind positive definiteness:
`⟪B⁺ v, v⟫ = ⟪B u, u⟫ + ⟪y, v⟫² / ⟪y, s⟫` with `u = v - (⟪B s, v⟫ / ⟪B s, s⟫) • s`. -/
private theorem inner_bfgsUpdate_self {B : E →L[ℝ] E} (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫)
    {s y : E} (hB : ⟪B s, s⟫ ≠ 0) (v : E) :
    ⟪bfgsUpdate B s y v, v⟫ =
      ⟪B (v - (⟪B s, v⟫ / ⟪B s, s⟫) • s), v - (⟪B s, v⟫ / ⟪B s, s⟫) • s⟫ +
        ⟪y, v⟫ ^ 2 / ⟪y, s⟫ := by
  have hvs : ⟪B v, s⟫ = ⟪B s, v⟫ := by rw [hsymm, real_inner_comm]
  simp only [bfgsUpdate_apply, map_sub, map_smul, inner_add_left, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, hvs]
  field_simp
  ring

/-- **The BFGS update preserves positive definiteness under the curvature condition.** If `B` is
symmetric and positive definite, `s ≠ 0` and `⟪y, s⟫ > 0`, then `B⁺` is positive definite
(Dennis and Schnabel 1983, Section 9.2). -/
theorem bfgsUpdate_pos {B : E →L[ℝ] E} (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪B v, v⟫) {s y : E} (hs : s ≠ 0) (hy : 0 < ⟪y, s⟫) :
    ∀ v, v ≠ 0 → 0 < ⟪bfgsUpdate B s y v, v⟫ := by
  intro v hv
  have hBs := hpos s hs
  rw [inner_bfgsUpdate_self hsymm hBs.ne']
  set t := ⟪B s, v⟫ / ⟪B s, s⟫
  rcases eq_or_ne (v - t • s) 0 with hu | hu
  · have hvt : v = t • s := sub_eq_zero.mp hu
    have ht : t ≠ 0 := by rintro h; rw [h, zero_smul] at hvt; exact hv hvt
    rw [hu, map_zero, inner_zero_left, zero_add, hvt, real_inner_smul_right]
    have : 0 < t ^ 2 := by positivity
    rw [mul_pow, mul_div_assoc, pow_two ⟪y, s⟫, mul_self_div_self]
    positivity
  · have h1 := hpos _ hu
    have h2 : 0 ≤ ⟪y, v⟫ ^ 2 / ⟪y, s⟫ := by positivity
    linarith

/-- **Curvature is necessary for a positive definite secant update.** If `B⁺ = bfgsUpdate B s y`
is positive definite, `s ≠ 0`, `⟪B s, s⟫ ≠ 0` and `⟪y, s⟫ ≠ 0`, then `⟪y, s⟫ > 0`: by the secant
equation `⟪y, s⟫ = ⟪B⁺ s, s⟫` (for the BFGS update, the necessity of the curvature condition
discussed in Dennis and Schnabel 1983, Section 9.2). -/
theorem inner_pos_of_bfgsUpdate_pos {B : E →L[ℝ] E} {s y : E} (hs : s ≠ 0)
    (hB : ⟪B s, s⟫ ≠ 0) (hy : ⟪y, s⟫ ≠ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪bfgsUpdate B s y v, v⟫) : 0 < ⟪y, s⟫ := by
  simpa [bfgsUpdate_apply_self hB hy] using hpos s hs

end MathlibExt.Analysis.Optimization.QuasiNewton
