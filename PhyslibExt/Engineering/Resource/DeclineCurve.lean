/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Decline curves: exponential and hyperbolic rate and cumulative production

## i. Overview

Decline laws under one explicit rate/time/production unit
convention. The exponential law is `q(t) = qi * exp (-D * t)`
with initial rate `qi > 0` and decline constant `D > 0`, for `t ≥ 0`. The
cumulative production is `Np(t) = (qi - q(t)) / D`, bounded by the
mathematical asymptote `qi / D`. These are properties of the stipulated
law only, not recoverable-reserve or fit-validity claims. The `D = 0`
constant-rate boundary is the separate law `Np = qi * t`, never the
divided formula.

## ii. Key results

- `DeclineCurve.expCumulative_hasDerivAt`: the cumulative's derivative is
  the rate.
- `DeclineCurve.expCumulative_le_asymptote`: cumulative production stays
  below the mathematical asymptote `qi / D`.
- `DeclineCurve.constCumulative_hasDerivAt`: the separate constant-rate
  boundary law.
- `Decline.hyperbolic_cumulative_hasDerivAt`: for the restricted
  hyperbolic law with `0 < b < 1`, the cumulative's derivative is the rate.
- `Decline.hyperbolic_cumulative_nonneg_le`: hyperbolic cumulative
  production is nonnegative and bounded by its finite mathematical
  asymptote.

## iii. Table of contents

- A. Exponential decline and its cumulative
- B. The constant-rate boundary
- C. Restricted hyperbolic decline

## iv. References

- J. J. Arps, *Analysis of decline curves*, Trans. AIME 160 (1945),
  228-247 (exponential decline as the `b = 0` member of the decline
  family).
-/

@[expose] public section

namespace Engineering.Resource.DeclineCurve

/-- Exponential-decline production rate `q(t) = qi * exp (-D * t)`. -/
noncomputable def expRate (qi D t : ℝ) : ℝ :=
  qi * Real.exp (-D * t)

/-- Cumulative production `(qi - q(t)) / D` under exponential decline.
Meaningful for `D ≠ 0`; the physical regime is `D > 0`. -/
noncomputable def expCumulative (qi D t : ℝ) : ℝ :=
  (qi - expRate qi D t) / D

/-- Constant-rate cumulative production `qi * t`, the separate `D = 0`
boundary law. -/
noncomputable def constCumulative (qi t : ℝ) : ℝ :=
  qi * t

set_option linter.unusedVariables false in
/-- The cumulative in closed form: `qi * (1 - exp (-D * t)) / D`. -/
lemma expCumulative_eq {qi D t : ℝ} (hD : D ≠ 0) :
    expCumulative qi D t = qi * (1 - Real.exp (-D * t)) / D := by
  unfold expCumulative expRate
  ring

/-- The cumulative starts at zero. -/
lemma expCumulative_zero (qi D : ℝ) :
    expCumulative qi D 0 = 0 := by
  simp [expCumulative, expRate]

/-- **Cumulative production theorem.** The derivative of the cumulative
is the rate itself. -/
lemma expCumulative_hasDerivAt {qi D : ℝ} (hD : D ≠ 0) (t : ℝ) :
    HasDerivAt (expCumulative qi D) (expRate qi D t) t := by
  have hlin : HasDerivAt (fun t : ℝ => -D * t) (-D) t := by
    simpa using (hasDerivAt_id t).const_mul (-D)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-D * t))
      (Real.exp (-D * t) * -D) t :=
    hlin.exp
  have hrate : HasDerivAt (fun t : ℝ => qi * Real.exp (-D * t))
      (qi * (Real.exp (-D * t) * -D)) t :=
    hexp.const_mul qi
  have hval : (-(qi * (Real.exp (-D * t) * -D))) / D = expRate qi D t := by
    unfold expRate
    field_simp
  have h := hrate.const_sub qi |>.div_const D
  rw [hval] at h
  exact h

/-- Cumulative production is nonnegative in the physical regime. -/
lemma expCumulative_nonneg {qi D t : ℝ} (hqi : 0 < qi) (hD : 0 < D)
    (ht : 0 ≤ t) : 0 ≤ expCumulative qi D t := by
  rw [expCumulative_eq (ne_of_gt hD)]
  apply div_nonneg _ (le_of_lt hD)
  apply mul_nonneg (le_of_lt hqi)
  have hexp : Real.exp (-D * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hDt : 0 ≤ D * t := mul_nonneg (le_of_lt hD) ht
    linarith
  linarith

set_option linter.unusedVariables false in
/-- The mathematical asymptote bounds cumulative production. This is a
property of the stipulated law, not a reserves estimate. -/
lemma expCumulative_le_asymptote {qi D t : ℝ} (hqi : 0 < qi) (hD : 0 < D)
    (ht : 0 ≤ t) : expCumulative qi D t ≤ qi / D := by
  unfold expCumulative expRate
  rw [div_le_div_iff_of_pos_right hD]
  have hpos : 0 < qi * Real.exp (-D * t) := mul_pos hqi (Real.exp_pos _)
  linarith

set_option linter.unusedVariables false in
/-- Cumulative production is monotone in time in the physical regime. -/
lemma expCumulative_mono {qi D s t : ℝ} (hqi : 0 ≤ qi) (hD : 0 < D)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    expCumulative qi D s ≤ expCumulative qi D t := by
  unfold expCumulative expRate
  rw [div_le_div_iff_of_pos_right hD]
  have hexp : Real.exp (-D * t) ≤ Real.exp (-D * s) := by
    rw [Real.exp_le_exp]
    have hDs : D * s ≤ D * t := mul_le_mul_of_nonneg_left hst (le_of_lt hD)
    linarith
  have hmul : qi * Real.exp (-D * t) ≤ qi * Real.exp (-D * s) :=
    mul_le_mul_of_nonneg_left hexp hqi
  linarith

/-- At `D = 0` the rate law is the constant rate `qi`. -/
lemma expRate_zero_decline (qi t : ℝ) :
    expRate qi 0 t = qi := by
  simp [expRate]

/-- **Constant-rate boundary.** The derivative of `qi * t` is the constant
rate; this separate law, not division by `D = 0`, gives cumulative
production when there is no decline. -/
lemma constCumulative_hasDerivAt (qi t : ℝ) :
    HasDerivAt (constCumulative qi) qi t := by
  have h : HasDerivAt (fun s : ℝ => qi * s) qi t := by
    simpa using (hasDerivAt_id t).const_mul qi
  exact h

end Engineering.Resource.DeclineCurve

namespace Engineering.Resource.Decline

/-- Hyperbolic-decline production rate `qi * (1 + b * Di * t) ^ (-1 / b)`,
as a real power. With the conventions `x / 0 = 0`, `x ^ 0 = 1` and `0 ^ y = 0`
for `y ≠ 0`, it is `qi` when `b = 0`, and `0` where `1 + b * Di * t = 0` with
`b ≠ 0`; a negative base `x` gives `|x| ^ y * cos (π y)`. -/
noncomputable def hyperbolicRate (qi Di b t : ℝ) : ℝ :=
  qi * (1 + b * Di * t) ^ (-(1 : ℝ) / b)

/-- Hyperbolic cumulative production
`qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b)) / ((1 - b) * Di)`. With the
conventions `x / 0 = 0` and `x ^ 0 = 1`, it is `0` when `b = 1`, `Di = 0`
or `b = 0`; otherwise `0 ^ y = 0` for `y ≠ 0`, and a negative base `x`
gives `|x| ^ y * cos (π y)`. The intended domain is `qi > 0`, `Di > 0`,
`0 < b < 1` and `t ≥ 0`. -/
noncomputable def hyperbolic_cumulative (qi Di b t : ℝ) : ℝ :=
  qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b : ℝ)) / ((1 - b) * Di)

private lemma aux_base_pos {Di b t : ℝ} (hDi : 0 < Di) (hb0 : 0 < b) (ht : 0 ≤ t) :
    (0 : ℝ) < 1 + b * Di * t := by
  have h : (0 : ℝ) ≤ b * Di * t := mul_nonneg (mul_nonneg hb0.le hDi.le) ht
  linarith

/-- No production at time zero (for `b = 1` or `Di = 0`, where the
denominator vanishes, by the convention `x / 0 = 0`). -/
lemma hyperbolic_cumulative_zero (qi Di b : ℝ) :
    hyperbolic_cumulative qi Di b 0 = 0 := by
  simp [hyperbolic_cumulative, Real.one_rpow]

/-- **Cumulative production theorem.** The derivative of the cumulative
is the hyperbolic rate, on the positive real-power domain `qi > 0`,
`Di > 0`, `0 < b < 1`, `t ≥ 0`. -/
lemma hyperbolic_cumulative_hasDerivAt {qi Di b t : ℝ} (hqi : 0 < qi)
    (hDi : 0 < Di) (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 ≤ t) :
    HasDerivAt (hyperbolic_cumulative qi Di b) (hyperbolicRate qi Di b t) t := by
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hK : (0 : ℝ) < (1 - b) * Di := mul_pos h1b hDi
  have hK' : (1 - b) * Di ≠ 0 := ne_of_gt hK
  have hu : (0 : ℝ) < 1 + b * Di * t := aux_base_pos hDi hb0 ht
  have hexp : ((b - 1) / b : ℝ) - 1 = -(1 : ℝ) / b := by
    field_simp
    ring
  have hlin : HasDerivAt (fun s : ℝ => 1 + b * Di * s) (b * Di) t := by
    have h1 : HasDerivAt (fun s : ℝ => b * Di * s) (b * Di * 1) t :=
      (hasDerivAt_id' t).const_mul (b * Di)
    have h2 := HasDerivAt.const_add (1 : ℝ) h1
    have hder : b * Di * 1 = b * Di := by ring
    rwa [hder] at h2
  have hrpow : HasDerivAt (fun s : ℝ => (1 + b * Di * s) ^ ((b - 1) / b : ℝ))
      ((b * Di) * ((b - 1) / b) * (1 + b * Di * t) ^ (((b - 1) / b : ℝ) - 1)) t :=
    hlin.rpow_const (Or.inl (ne_of_gt hu))
  have hsub : HasDerivAt (fun s : ℝ => 1 - (1 + b * Di * s) ^ ((b - 1) / b : ℝ))
      (-((b * Di) * ((b - 1) / b) * (1 + b * Di * t) ^ (((b - 1) / b : ℝ) - 1))) t :=
    HasDerivAt.const_sub (1 : ℝ) hrpow
  have hmul : HasDerivAt (fun s : ℝ => qi * (1 - (1 + b * Di * s) ^ ((b - 1) / b : ℝ)))
      (qi * (-((b * Di) * ((b - 1) / b) * (1 + b * Di * t) ^ (((b - 1) / b : ℝ) - 1)))) t :=
    HasDerivAt.const_mul qi hsub
  have hdiv : HasDerivAt
      (fun s : ℝ => qi * (1 - (1 + b * Di * s) ^ ((b - 1) / b : ℝ)) / ((1 - b) * Di))
      ((qi * (-((b * Di) * ((b - 1) / b) * (1 + b * Di * t) ^ (((b - 1) / b : ℝ) - 1)))) /
        ((1 - b) * Di)) t :=
    hmul.div_const ((1 - b) * Di)
  have hderiv : (qi * (-((b * Di) * ((b - 1) / b) *
      (1 + b * Di * t) ^ (((b - 1) / b : ℝ) - 1)))) / ((1 - b) * Di)
      = hyperbolicRate qi Di b t := by
    rw [hexp]
    unfold hyperbolicRate
    field_simp
    ring
  have hfun : hyperbolic_cumulative qi Di b
      = fun s : ℝ => qi * (1 - (1 + b * Di * s) ^ ((b - 1) / b : ℝ)) / ((1 - b) * Di) := rfl
  rw [hfun, ← hderiv]
  exact hdiv

set_option linter.unusedVariables false in
/-- The equivalent rate form of the cumulative, for `qi > 0`, `Di > 0`,
`0 < b < 1` and `t ≥ 0`:
`qi ^ b * (qi ^ (1 - b) - q(t) ^ (1 - b)) / ((1 - b) * Di)`. -/
lemma hyperbolic_cumulative_eq_alt {qi Di b t : ℝ} (hqi : 0 < qi)
    (hDi : 0 < Di) (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 ≤ t) :
    hyperbolic_cumulative qi Di b t =
      qi ^ b * (qi ^ (1 - b : ℝ) - hyperbolicRate qi Di b t ^ (1 - b : ℝ)) /
        ((1 - b) * Di) := by
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hu : (0 : ℝ) < 1 + b * Di * t := aux_base_pos hDi hb0 ht
  have hexp : (-(1 : ℝ) / b) * (1 - b) = ((b - 1) / b : ℝ) := by
    field_simp
    ring
  have hq : hyperbolicRate qi Di b t ^ (1 - b : ℝ)
      = qi ^ (1 - b : ℝ) * (1 + b * Di * t) ^ ((b - 1) / b : ℝ) := by
    unfold hyperbolicRate
    rw [Real.mul_rpow hqi.le (Real.rpow_nonneg hu.le _)]
    congr 1
    rw [← Real.rpow_mul hu.le, hexp]
  have hA : qi ^ (b : ℝ) * qi ^ (1 - b : ℝ) = qi := by
    rw [← Real.rpow_add hqi]
    have hsum : (b : ℝ) + (1 - b) = 1 := by ring
    rw [hsum, Real.rpow_one]
  unfold hyperbolic_cumulative
  rw [hq]
  have hcalc : qi ^ b * (qi ^ (1 - b : ℝ) -
      qi ^ (1 - b : ℝ) * (1 + b * Di * t) ^ ((b - 1) / b : ℝ))
      = qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b : ℝ)) := by
    calc qi ^ b * (qi ^ (1 - b : ℝ) -
            qi ^ (1 - b : ℝ) * (1 + b * Di * t) ^ ((b - 1) / b : ℝ))
          = (qi ^ (b : ℝ) * qi ^ (1 - b : ℝ)) * (1 - (1 + b * Di * t) ^ ((b - 1) / b : ℝ)) := by
            ring
        _ = qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b : ℝ)) := by rw [hA]
  rw [hcalc]

/-- The rate stays positive in the physical regime `qi > 0`, `Di > 0`,
`b > 0`, `t ≥ 0`. -/
lemma hyperbolicRate_pos {qi Di b t : ℝ} (hqi : 0 < qi) (hDi : 0 < Di)
    (hb0 : 0 < b) (ht : 0 ≤ t) : 0 < hyperbolicRate qi Di b t := by
  unfold hyperbolicRate
  exact mul_pos hqi (Real.rpow_pos_of_pos (aux_base_pos hDi hb0 ht) _)

/-- For `qi > 0`, `Di > 0`, `0 < b < 1` and `t ≥ 0`, cumulative production
is nonnegative and bounded by the finite
mathematical asymptote `qi / ((1 - b) * Di)`, which is not a reserve
estimate. -/
lemma hyperbolic_cumulative_nonneg_le {qi Di b t : ℝ} (hqi : 0 < qi)
    (hDi : 0 < Di) (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 ≤ t) :
    0 ≤ hyperbolic_cumulative qi Di b t ∧
      hyperbolic_cumulative qi Di b t ≤ qi / ((1 - b) * Di) := by
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hK : (0 : ℝ) < (1 - b) * Di := mul_pos h1b hDi
  have hu : (0 : ℝ) < 1 + b * Di * t := aux_base_pos hDi hb0 ht
  have hu1 : (1 : ℝ) ≤ 1 + b * Di * t := by
    have h : (0 : ℝ) ≤ b * Di * t := mul_nonneg (mul_nonneg hb0.le hDi.le) ht
    linarith
  have hc : ((b - 1 : ℝ) / b) ≤ 0 := by
    rw [div_le_iff₀ hb0, zero_mul]
    linarith
  have hU1 : (1 + b * Di * t) ^ ((b - 1) / b : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu1 hc
  have hU0 : (0 : ℝ) < (1 + b * Di * t) ^ ((b - 1) / b : ℝ) :=
    Real.rpow_pos_of_pos hu _
  unfold hyperbolic_cumulative
  constructor
  · exact div_nonneg (mul_nonneg hqi.le (by linarith)) hK.le
  · rw [div_le_div_iff_of_pos_right hK]
    calc qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b : ℝ)) ≤ qi * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) hqi.le
      _ = qi := mul_one qi

end Engineering.Resource.Decline
