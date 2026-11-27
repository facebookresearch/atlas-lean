/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Barzilai–Borwein step sizes

The two-point step-size gradient method of Barzilai and Borwein iterates
`x (k + 1) = x k - α k • ∇f(x k)`, where, with `s = x k - x (k - 1)` and
`y = ∇f(x k) - ∇f(x (k - 1))`, the step size `α k` makes `α⁻¹ I` (or `α I`) a least-squares fit
of the secant equation:

* `α = ‖s‖² / ⟪s, y⟫` minimises `‖α⁻¹ s - y‖` (Y. H. Dai, J. Y. Yuan and Y. Yuan, *Modified
  two-point stepsize gradient methods for unconstrained optimization*, Comput. Optim. Appl. 22
  (2002), 103-109, formula (1.5));
* `α = ⟪s, y⟫ / ‖y‖²` minimises `‖s - α y‖` (the second Barzilai–Borwein formula; W. Yin, UCLA
  Math 164 lecture notes *Barzilai–Borwein method*, 2015).

We prove both least-squares characterisations, the ordering of the two step sizes, and that on a
quadratic with Hessian `A` (where `y = A s`) the inverse of the first step size is a Rayleigh
quotient of `A`, so the step lies between the inverses of the curvature bounds (the
interpretation in Section 2 of Dai, Yuan and Yuan 2002).
-/

@[expose] public section

namespace MathlibExt.Analysis.Optimization.BarzilaiBorwein

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **First Barzilai–Borwein step size.** `α = ‖s‖² / ⟪s, y⟫` for the step `s` and gradient change
`y` (Dai, Yuan and Yuan, Comput. Optim. Appl. 22 (2002), formula (1.5)). -/
noncomputable def bbStep (s y : E) : ℝ := ‖s‖ ^ 2 / ⟪s, y⟫

/-- **Second Barzilai–Borwein step size.** `α = ⟪s, y⟫ / ‖y‖²` for the step `s` and gradient
change `y` (W. Yin, UCLA Math 164 lecture notes *Barzilai–Borwein method*, 2015). -/
noncomputable def bbStep₂ (s y : E) : ℝ := ⟪s, y⟫ / ‖y‖ ^ 2

/-- **The first Barzilai–Borwein step is a least-squares secant fit.** For every `t`,
`‖α⁻¹ s - y‖ ≤ ‖t s - y‖` with `α = ‖s‖² / ⟪s, y⟫`: the scalar matrix `α⁻¹ I` best satisfies the
secant equation `B s = y` (Dai, Yuan and Yuan, Comput. Optim. Appl. 22 (2002), Section 1: "By
minimizing `‖H_k⁻¹ s_{k-1} - y_{k-1}‖₂` they obtained (1.5)"). -/
theorem norm_inv_bbStep_smul_sub_le (s y : E) (t : ℝ) :
    ‖(bbStep s y)⁻¹ • s - y‖ ≤ ‖t • s - y‖ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hS : 0 < ‖s‖ ^ 2 := by have := norm_pos_iff.mpr hs; positivity
  have hinv : (bbStep s y)⁻¹ = ⟪s, y⟫ / ‖s‖ ^ 2 := by rw [bbStep, inv_div]
  rw [hinv]
  apply pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_left]
  have key : (⟪s, y⟫ / ‖s‖ ^ 2) ^ 2 * ‖s‖ ^ 2 - 2 * (⟪s, y⟫ / ‖s‖ ^ 2 * ⟪s, y⟫) =
      -(⟪s, y⟫ ^ 2 / ‖s‖ ^ 2) := by field_simp; ring
  have key2 : t ^ 2 * ‖s‖ ^ 2 - 2 * (t * ⟪s, y⟫) + ⟪s, y⟫ ^ 2 / ‖s‖ ^ 2 =
      (t * ‖s‖ ^ 2 - ⟪s, y⟫) ^ 2 / ‖s‖ ^ 2 := by field_simp; ring
  have : 0 ≤ (t * ‖s‖ ^ 2 - ⟪s, y⟫) ^ 2 / ‖s‖ ^ 2 := by positivity
  linarith

/-- **The second Barzilai–Borwein step is a least-squares secant fit.** For every `t`,
`‖s - α y‖ ≤ ‖s - t y‖` with `α = ⟪s, y⟫ / ‖y‖²` (W. Yin, UCLA Math 164 lecture notes
*Barzilai–Borwein method*, 2015). -/
theorem norm_sub_bbStep₂_smul_le (s y : E) (t : ℝ) :
    ‖s - bbStep₂ s y • y‖ ≤ ‖s - t • y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hY : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.mpr hy; positivity
  apply pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_right,
    real_inner_smul_right, bbStep₂]
  have key : -(2 * (⟪s, y⟫ / ‖y‖ ^ 2 * ⟪s, y⟫)) + (⟪s, y⟫ / ‖y‖ ^ 2) ^ 2 * ‖y‖ ^ 2 =
      -(⟪s, y⟫ ^ 2 / ‖y‖ ^ 2) := by field_simp; ring
  have key2 : -(2 * (t * ⟪s, y⟫)) + t ^ 2 * ‖y‖ ^ 2 + ⟪s, y⟫ ^ 2 / ‖y‖ ^ 2 =
      (t * ‖y‖ ^ 2 - ⟪s, y⟫) ^ 2 / ‖y‖ ^ 2 := by field_simp; ring
  have : 0 ≤ (t * ‖y‖ ^ 2 - ⟪s, y⟫) ^ 2 / ‖y‖ ^ 2 := by positivity
  linarith

/-- **The second Barzilai–Borwein step is the shorter one.** If `⟪s, y⟫ > 0`, then
`⟪s, y⟫ / ‖y‖² ≤ ‖s‖² / ⟪s, y⟫`, by the Cauchy–Schwarz inequality `⟪s, y⟫² ≤ ‖s‖² ‖y‖²`. -/
theorem bbStep₂_le_bbStep {s y : E} (h : 0 < ⟪s, y⟫) : bbStep₂ s y ≤ bbStep s y := by
  have hy : y ≠ 0 := by rintro rfl; simp at h
  have hY : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.mpr hy; positivity
  rw [bbStep₂, bbStep, div_le_div_iff₀ hY h]
  have hcs := abs_real_inner_le_norm s y
  have : ⟪s, y⟫ ≤ ‖s‖ * ‖y‖ := (le_abs_self _).trans hcs
  nlinarith

/-- **Barzilai–Borwein steps on a quadratic lie between the inverse curvature bounds.** Let `A` be
a linear operator with `m ‖v‖² ≤ ⟪A v, v⟫ ≤ L ‖v‖²` for all `v`, where `0 < m`, and let `s ≠ 0`.
For the gradient change `y = A s` of the quadratic `½ ⟪A x, x⟫ - ⟪b, x⟫`, the inverse step
`1 / α = ⟪s, A s⟫ / ‖s‖²` is a Rayleigh quotient of `A`, so `1 / L ≤ α ≤ 1 / m`. This makes precise
the remark in Section 2 of Dai, Yuan and Yuan (2002) that (1.5) approximates the inverse of the
second directional derivative of `f` along `s`. -/
theorem bbStep_mem_Icc {A : E →L[ℝ] E} {m L : ℝ} (hm : 0 < m)
    (hlow : ∀ v, m * ‖v‖ ^ 2 ≤ ⟪A v, v⟫) (hup : ∀ v, ⟪A v, v⟫ ≤ L * ‖v‖ ^ 2) {s : E}
    (hs : s ≠ 0) : 1 / L ≤ bbStep s (A s) ∧ bbStep s (A s) ≤ 1 / m := by
  have hS : 0 < ‖s‖ ^ 2 := by have := norm_pos_iff.mpr hs; positivity
  have h1 := hlow s
  have h2 := hup s
  rw [real_inner_comm] at h1 h2
  have hq : 0 < ⟪s, A s⟫ := by nlinarith
  have hL : 0 < L := by nlinarith
  unfold bbStep
  constructor
  · rw [div_le_div_iff₀ hL hq]; linarith
  · rw [div_le_div_iff₀ hq hm]; linarith

end MathlibExt.Analysis.Optimization.BarzilaiBorwein
