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
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exponential decline: rate and cumulative production

## i. Overview

Exponential decline under one explicit rate/time/production unit
convention: the stipulated empirical rate law is `q(t) = qi * exp (-D * t)`
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

## iii. Table of contents

- A. Exponential decline and its cumulative
- B. The constant-rate boundary

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
