/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellRotatedSquare
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Inverting the sum of the Pell interpolating functions

The smaller quadratic root gives the first coordinate `z` of the point on
`u² - D v² = 1` with nonnegative coordinates and `u + v = x`.
-/

namespace MetaMathlibExt

namespace pell_inverse_closed_form

private theorem inverse_coordinates {d x : ℝ} (hd : 1 < d) (hx : 1 ≤ x) :
    let z := (d * x - Real.sqrt (d * x ^ 2 - d + 1)) / (d - 1)
    1 ≤ z ∧ Real.sqrt (z ^ 2 - 1) = Real.sqrt d * (x - z) := by
  intro z
  let r := Real.sqrt (d * x ^ 2 - d + 1)
  have hd₀ := sub_pos.mpr hd
  have hx₂ : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hxr : x ≤ r := Real.le_sqrt_of_sq_le (by
    nlinarith only [mul_nonneg hd₀.le (sub_nonneg.mpr hx₂)])
  have hr₂ : r ^ 2 = d * x ^ 2 - d + 1 := Real.sq_sqrt (by
    nlinarith only [mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hx₂)])
  have hz : z * (d - 1) = d * x - r := div_mul_cancel₀ _ hd₀.ne'
  have hz₁ : 1 ≤ z := by
    apply (le_div_iff₀ hd₀).2
    have hr : r ≤ d * (x - 1) + 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · nlinarith only [mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hx)]
      · nlinarith only [mul_nonneg (mul_nonneg (zero_lt_one.trans hd).le hd₀.le)
          (sq_nonneg (x - 1))]
    linarith
  have hzx : z ≤ x := by
    apply (div_le_iff₀ hd₀).2
    linarith
  -- The defining quadratic gives the norm equation for (z, x - z).
  have hnorm : z ^ 2 - 1 = d * (x - z) ^ 2 := by
    apply mul_left_cancel₀ hd₀.ne'
    linear_combination (d * x - z * (d - 1) + r) * hz - hr₂
  refine ⟨hz₁, ?_⟩
  rw [hnorm, Real.sqrt_mul (zero_lt_one.trans hd).le, Real.sqrt_sq (sub_nonneg.mpr hzx)]

end pell_inverse_closed_form

/-- **Closed form for inverting the sum of the Pell interpolating functions.** Let $D$ be an
integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation $X^2 - D Y^2 = 1$,
put $\varepsilon = \alpha + \beta \sqrt{D}$ and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(t) = (\varepsilon^t + \bar\varepsilon^t) / 2$ and
$v(t) = (\varepsilon^t - \bar\varepsilon^t) / (2 \sqrt{D})$ for real $t$. For every real $x \ge 1$,
put $z = (D x - \sqrt{D x^2 - D + 1}) / (D - 1)$ and
$g = \log(z + \sqrt{z^2 - 1}) / \log \varepsilon$. Then $g \ge 0$ and $u(g) + v(g) = x$.

Here $\log(z + \sqrt{z^2 - 1})$ is $\cosh^{-1}(z)$ written in logarithmic form.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.2, Equation (2.1)
(`integers-2025-A112-thm-2-2`). -/
public theorem pell_inverse_closed_form {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x : ℝ} (hx : 1 ≤ x) :
    let z : ℝ := (D * x - Real.sqrt (D * x ^ 2 - D + 1)) / (D - 1)
    let g : ℝ := Real.log (z + Real.sqrt (z ^ 2 - 1)) / Real.log (a.x + a.y * Real.sqrt D)
    0 ≤ g ∧ pellU D a.x a.y g + pellV D a.x a.y g = x := by
  intro z g
  have hD : (1 : ℝ) < D := by
    have hne : D ≠ 1 := fun h => ha.d_nonsquare (h ▸ IsSquare.one)
    have hpos := ha.d_pos
    exact_mod_cast (show (1 : ℤ) < D by omega)
  obtain ⟨hz, hrad⟩ := pell_inverse_closed_form.inverse_coordinates hD hx
  let ε : ℝ := a.x + a.y * Real.sqrt D
  have hε : 1 < ε := by
    have hα : 1 < (a.x : ℝ) := by exact_mod_cast ha.1
    have hβ : 0 ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1.le
    exact lt_add_of_lt_of_nonneg hα (mul_nonneg hβ (Real.sqrt_nonneg _))
  let s := Real.sqrt (z ^ 2 - 1)
  have harg : 1 ≤ z + s := le_add_of_le_of_nonneg hz (Real.sqrt_nonneg _)
  have hpow : ε ^ g = z + s :=
    Real.rpow_logb (zero_lt_one.trans hε) hε.ne' (zero_lt_one.trans_le harg)
  have hconj : (a.x : ℝ) - a.y * Real.sqrt D = ε⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (zero_lt_one.trans hε).ne').mp
    change (_ - _) * (_ + _) = 1
    rw [mul_comm, ← sq_sub_sq, mul_pow, Real.sq_sqrt (zero_lt_one.trans hD).le, mul_comm _ (D : ℝ)]
    exact_mod_cast a.prop
  have hinv : (z + s)⁻¹ = z - s := by
    apply (mul_eq_one_iff_inv_eq₀ (zero_lt_one.trans_le harg).ne').mp
    rw [← sq_sub_sq]
    have hs : s ^ 2 = z ^ 2 - 1 := Real.sq_sqrt (sub_nonneg.mpr (one_le_pow₀ hz))
    linarith
  refine ⟨Real.logb_nonneg hε harg, ?_⟩
  unfold pellU pellV
  change (ε ^ g + _ ^ g) / 2 + (ε ^ g - _ ^ g) / (2 * Real.sqrt D) = x
  rw [hconj, Real.inv_rpow (zero_lt_one.trans hε).le, hpow, hinv]
  rw [show s = Real.sqrt D * (x - z) from hrad]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (zero_lt_one.trans hD))]
  ring

end MetaMathlibExt
