/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Real.Sqrt

/-!
# Muscle power maximum for the Hill shortening hyperbola

## i. Overview

For the shortening velocity law `v(F) = b * (F0 - F) / (F + a)` with
`a, b, F0 > 0`, the power `P(F) = F * v(F)` on `[0, F0]` attains its
maximum at the strictly interior force
`Fstar = sqrt (a * (a + F0)) - a`. This is the selected empirical
shortening hyperbola only: no eccentric or lengthening claim, and no
claim outside `[0, F0]`.

## ii. Key results

* `muscle_power_max`: interiority of `Fstar`, its defining identity
  `Fstar^2 + 2 * a * Fstar = a * F0`, and maximality of the power.
* `muscle_power_formula`, `muscle_work_constant`: mechanical power at a
  force, and work at constant force as `c * (x T - x 0)`.

## iii. Table of contents

* A. The power maximum.
* B. Power and work.

## iv. References

* A. V. Hill, "The heat of shortening and the dynamic constants of
  muscle", Proc. R. Soc. B 126 (1938), 136-195: the shortening
  hyperbola `(F + a) * v = b * (F0 - F)`. The result below is an
  elementary consequence of the declared law, hence a `lemma`.

-/

@[expose] public section

open Real intervalIntegral

namespace PhyslibExt.Biomechanics.MusclePower

/-! ## A. The power maximum. -/

/-- **Muscle power maximum (Hill shortening hyperbola).** For the
shortening velocity law `v(F) = b * (F0 - F) / (F + a)` with
`a, b, F0 > 0`, the power `P(F) = F * v(F)` on `[0, F0]` attains its
maximum at the strictly interior point
`Fstar = sqrt (a * (a + F0)) - a`, which satisfies
`Fstar^2 + 2 * a * Fstar = a * F0`. This is the selected empirical
shortening hyperbola only: no eccentric/lengthening claim. -/
lemma muscle_power_max {a b F0 : ℝ} (ha : 0 < a) (hb : 0 < b) (hF0 : 0 < F0) :
    let Fstar := Real.sqrt (a * (a + F0)) - a
    0 < Fstar ∧ Fstar < F0 ∧ Fstar ^ 2 + 2 * a * Fstar = a * F0 ∧
    ∀ F : ℝ, 0 ≤ F → F ≤ F0 →
      F * (b * (F0 - F) / (F + a)) ≤ Fstar * (b * (F0 - Fstar) / (Fstar + a)) := by
  change 0 < (Real.sqrt (a * (a + F0)) - a) ∧
    (Real.sqrt (a * (a + F0)) - a) < F0 ∧
    (Real.sqrt (a * (a + F0)) - a) ^ 2 + 2 * a * (Real.sqrt (a * (a + F0)) - a) = a * F0 ∧
    ∀ F : ℝ, 0 ≤ F → F ≤ F0 →
      F * (b * (F0 - F) / (F + a)) ≤
        (Real.sqrt (a * (a + F0)) - a) *
          (b * (F0 - (Real.sqrt (a * (a + F0)) - a)) /
            ((Real.sqrt (a * (a + F0)) - a) + a))
  have haF0 : 0 < a + F0 := by linarith
  have harg : 0 ≤ a * (a + F0) := le_of_lt (mul_pos ha haF0)
  have hsq : (Real.sqrt (a * (a + F0))) ^ 2 = a * (a + F0) := Real.sq_sqrt harg
  have hsqrt_pos : 0 < Real.sqrt (a * (a + F0)) := Real.sqrt_pos.2 (mul_pos ha haF0)
  have h_a_lt : a < Real.sqrt (a * (a + F0)) := by
    rw [Real.lt_sqrt (le_of_lt ha)]
    have h : 0 < a * F0 := mul_pos ha hF0
    nlinarith [h]
  have h_lt : Real.sqrt (a * (a + F0)) < F0 + a := by
    rw [Real.sqrt_lt' (by linarith : 0 < F0 + a)]
    have h : 0 < F0 * (F0 + a) := mul_pos hF0 (by linarith : 0 < F0 + a)
    nlinarith [h]
  have hpos : 0 < Real.sqrt (a * (a + F0)) - a := by linarith
  have hltF0 : Real.sqrt (a * (a + F0)) - a < F0 := by linarith
  have hid : (Real.sqrt (a * (a + F0)) - a) ^ 2 +
      2 * a * (Real.sqrt (a * (a + F0)) - a) = a * F0 := by
    linear_combination hsq
  refine ⟨hpos, hltF0, hid, ?_⟩
  intro F hF0 hFF0
  have hFa : 0 < F + a := by linarith
  have hFsa : 0 < (Real.sqrt (a * (a + F0)) - a) + a := by linarith
  have hne1 : F + a ≠ 0 := ne_of_gt hFa
  have hne2 : (Real.sqrt (a * (a + F0)) - a) + a ≠ 0 := ne_of_gt hFsa
  have hne_a : a ≠ 0 := ne_of_gt ha
  have hkey : a * (F0 - (Real.sqrt (a * (a + F0)) - a)) =
      (Real.sqrt (a * (a + F0)) - a) * ((Real.sqrt (a * (a + F0)) - a) + a) := by
    linear_combination -hid
  have hfrac : (F0 - (Real.sqrt (a * (a + F0)) - a)) /
      ((Real.sqrt (a * (a + F0)) - a) + a) =
      (Real.sqrt (a * (a + F0)) - a) / a := by
    rw [div_eq_div_iff hne2 hne_a]
    linear_combination hkey
  have hPstar : (Real.sqrt (a * (a + F0)) - a) *
      (b * (F0 - (Real.sqrt (a * (a + F0)) - a)) /
        ((Real.sqrt (a * (a + F0)) - a) + a)) =
      b * (Real.sqrt (a * (a + F0)) - a) ^ 2 / a := by
    have h1 : b * (F0 - (Real.sqrt (a * (a + F0)) - a)) /
        ((Real.sqrt (a * (a + F0)) - a) + a) =
        b * ((Real.sqrt (a * (a + F0)) - a) / a) := by
      rw [← hfrac]
      ring
    rw [h1]
    ring
  rw [hPstar]
  have hdiff : b * (Real.sqrt (a * (a + F0)) - a) ^ 2 / a -
      F * (b * (F0 - F) / (F + a)) =
      b * (F - (Real.sqrt (a * (a + F0)) - a)) ^ 2 / (F + a) := by
    field_simp
    linear_combination F * hid
  have hnonneg : 0 ≤ b * (F - (Real.sqrt (a * (a + F0)) - a)) ^ 2 / (F + a) := by
    apply div_nonneg _ (le_of_lt hFa)
    apply mul_nonneg (le_of_lt hb)
    exact sq_nonneg _
  linarith

/-! ## B. Power and work. -/

/-- Hill shortening velocity at force `F`: `v(F) = b (F0 - F)/(F + a)`. -/
noncomputable def hillVelocity (a b F0 F : ℝ) : ℝ := b * (F0 - F) / (F + a)

/-- Mechanical power at force `F`: `P(F) = F * v(F)`. -/
noncomputable def hillPower (a b F0 F : ℝ) : ℝ := F * hillVelocity a b F0 F

/-- Hill velocity formula. -/
lemma hillVelocity_eq {a b F0 F : ℝ} :
    hillVelocity a b F0 F = b * (F0 - F) / (F + a) := rfl

set_option linter.unusedVariables false in
/-- **Mechanical power under the Hill law.** On the declared domain
(`a, b, F0 > 0`, `F ∈ [0, F0]`), the mechanical power is
`P(F) = b * F * (F0 - F) / (F + a)`. -/
lemma muscle_power_formula {a b F0 F : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hF0 : 0 < F0) (hF : F ∈ Set.Icc 0 F0) :
    hillPower a b F0 F = b * F * (F0 - F) / (F + a) := by
  rw [hillPower, hillVelocity_eq]
  ring

set_option linter.unusedVariables false in
/-- **Work at constant force.** If the displacement `x` has constant
derivative `x' = v(c) = b * (F0 - c) / (c + a)` (constant force `c`
under the Hill law), then the mechanical work over `[0, T]`, the time
integral of the power `c * x'`, equals `c * (x T - x 0)`. -/
lemma muscle_work_constant {a b F0 c T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hF0 : 0 < F0) (hc : c ∈ Set.Icc 0 F0) (hT : 0 ≤ T) {x : ℝ → ℝ}
    (hx : ∀ t ∈ Set.uIcc 0 T, HasDerivAt x (b * (F0 - c) / (c + a)) t) :
    (∫ _t in (0:ℝ)..T, c * (b * (F0 - c) / (c + a))) = c * (x T - x 0) := by
  have hFTC : (∫ _t in (0:ℝ)..T, b * (F0 - c) / (c + a)) = x T - x 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hx intervalIntegrable_const
  calc (∫ _t in (0:ℝ)..T, c * (b * (F0 - c) / (c + a)))
      = c * (∫ _t in (0:ℝ)..T, b * (F0 - c) / (c + a)) :=
        intervalIntegral.integral_const_mul c _
    _ = c * (x T - x 0) := by rw [hFTC]

end PhyslibExt.Biomechanics.MusclePower
