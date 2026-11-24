/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Linear IS-LM system and policy comparative statics

IS: `Y + b * r = A`. LM: `k * Y - h * r = M`. Under the slope signs `0 < b`,
`0 < h`, `0 < k` the system matrix `[[1, b], [k, -h]]` is nonsingular, with explicit
solution `Y = (h * A + b * M) / (h + b * k)`, `r = (k * A - M) / (h + b * k)`.
Fiscal expansion raises `Y` and `r`; monetary expansion raises `Y` and lowers `r`.

## Main results

* `MathlibExt.Economics.Macro.ISLM.islm_solution`: explicit solution.
* `MathlibExt.Economics.Macro.ISLM.islm_fiscal_expansion`: fiscal comparative statics.
* `MathlibExt.Economics.Macro.ISLM.islm_monetary_expansion`: monetary comparative statics.
-/

namespace MathlibExt.Economics.Macro.ISLM

/-- The linear IS-LM system. Parameters: `b > 0` is the interest sensitivity of
investment/demand, `h > 0` the interest sensitivity of money demand, `k > 0` the income
sensitivity of money demand. Variables: `Y` output, `r` interest rate. Exogenous:
`A` autonomous spending (IS intercept), `M` real money supply (LM intercept).
IS: `Y + b * r = A`. LM: `k * Y - h * r = M`.
In matrix form the system matrix is `[[1, b], [k, -h]]` with determinant `-(h + b * k)`. -/
def IsISLM (b h k A M Y r : ℝ) : Prop :=
  Y + b * r = A ∧ k * Y - h * r = M

/-- **IS-LM solution (MA06.T02).** Under the slope-sign restrictions `0 < b`, `0 < h`,
`0 < k`, the nonsingular system has the explicit solution
`Y = (h * A + b * M) / (h + b * k)` and `r = (k * A - M) / (h + b * k)`.
This is the explicit 2x2 Cramer-rule solution, proved by elimination on the two scalar
equations. It develops no general matrix-inversion theory, and it neither uses nor
reproves `Matrix.mul_nonsing_inv` (which states `A * A⁻¹ = 1`, not the solution formula);
the scalar solution is the usable form. -/
theorem islm_solution {b h k A M Y r : ℝ} (hb : 0 < b) (hh : 0 < h) (hk : 0 < k)
    (hsys : IsISLM b h k A M Y r) :
    Y = (h * A + b * M) / (h + b * k) ∧ r = (k * A - M) / (h + b * k) := by
  obtain ⟨hIS, hLM⟩ := hsys
  have hpos : 0 < h + b * k := by positivity
  have hne : h + b * k ≠ 0 := ne_of_gt hpos
  have hY : (h + b * k) * Y = h * A + b * M := by
    linear_combination h * hIS + b * hLM
  have hr : (h + b * k) * r = k * A - M := by
    linear_combination k * hIS - hLM
  constructor
  · rw [eq_div_iff hne]
    linear_combination hY
  · rw [eq_div_iff hne]
    linear_combination hr

/-- **Fiscal expansion (MA06.T02).** Holding the money supply fixed, a rise in autonomous
spending raises both output and the interest rate. -/
theorem islm_fiscal_expansion {b h k A₁ A₂ M Y₁ Y₂ r₁ r₂ : ℝ} (hb : 0 < b) (hh : 0 < h)
    (hk : 0 < k) (hA : A₁ < A₂) (h₁ : IsISLM b h k A₁ M Y₁ r₁)
    (h₂ : IsISLM b h k A₂ M Y₂ r₂) : Y₁ < Y₂ ∧ r₁ < r₂ := by
  obtain ⟨hY₁, hr₁⟩ := islm_solution hb hh hk h₁
  obtain ⟨hY₂, hr₂⟩ := islm_solution hb hh hk h₂
  have hpos : 0 < h + b * k := by positivity
  have hY : h * A₁ + b * M < h * A₂ + b * M := by
    have hmul : h * A₁ < h * A₂ := mul_lt_mul_of_pos_left hA hh
    linarith
  have hr : k * A₁ - M < k * A₂ - M := by
    have hmul : k * A₁ < k * A₂ := mul_lt_mul_of_pos_left hA hk
    linarith
  rw [hY₁, hY₂, hr₁, hr₂]
  exact ⟨div_lt_div_of_pos_right hY hpos, div_lt_div_of_pos_right hr hpos⟩

/-- **Monetary expansion (MA06.T02).** Holding autonomous spending fixed, a rise in the
money supply raises output and lowers the interest rate. -/
theorem islm_monetary_expansion {b h k A M₁ M₂ Y₁ Y₂ r₁ r₂ : ℝ} (hb : 0 < b) (hh : 0 < h)
    (hk : 0 < k) (hM : M₁ < M₂) (h₁ : IsISLM b h k A M₁ Y₁ r₁)
    (h₂ : IsISLM b h k A M₂ Y₂ r₂) : Y₁ < Y₂ ∧ r₂ < r₁ := by
  obtain ⟨hY₁, hr₁⟩ := islm_solution hb hh hk h₁
  obtain ⟨hY₂, hr₂⟩ := islm_solution hb hh hk h₂
  have hpos : 0 < h + b * k := by positivity
  have hY : h * A + b * M₁ < h * A + b * M₂ := by
    have hmul : b * M₁ < b * M₂ := mul_lt_mul_of_pos_left hM hb
    linarith
  have hr : k * A - M₂ < k * A - M₁ := by linarith
  rw [hY₁, hY₂, hr₁, hr₂]
  exact ⟨div_lt_div_of_pos_right hY hpos, div_lt_div_of_pos_right hr hpos⟩

end MathlibExt.Economics.Macro.ISLM
