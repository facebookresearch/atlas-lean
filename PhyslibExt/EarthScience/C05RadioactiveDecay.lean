/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
/-!
# Radioactive decay and the unique positive half-life

For decay constant `λ > 0` and initial inventory `N0 > 0`,
`N(t) = N0 * exp(-λ*t)` solves `N' = -λ*N` and has the unique positive
half-life `log 2 / λ`.

## i. Overview

Constant single-parent decay law on `t ≥ 0`. Initial daughter and
branching are not needed for this result. The clock law is stipulated,
not empirically certified: this file proves the mathematics of the
exponential clock, not that any sample obeys it.

## ii. Key results

- `EarthScience.decay_hasDerivAt`: `N(t) = N0*exp(-λ*t)` satisfies `N' = -λ*N`.
- `EarthScience.decay_halfLife_value`: `N(log 2 / λ) = N0 / 2`.
- `EarthScience.decay_halfLife_unique`: any `t ≥ 0` with `N(t) = N0/2`
  equals `log 2 / λ`.

## iii. References

- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
- `Real.exp_log`, `Real.exp_injective` for the half-life algebra.
-/

@[expose] public section

namespace EarthScience

/-- Radioactive decay: `N(t) = N0 * exp(-λ*t)` solves `N' = -λ*N`. -/
theorem decay_hasDerivAt (lam N0 t : ℝ) :
    HasDerivAt (fun t => N0 * Real.exp (-lam * t))
      (-lam * (N0 * Real.exp (-lam * t))) t := by
  have hlin : HasDerivAt (fun t : ℝ => -lam * t) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp := hlin.exp
  have hmul := hexp.const_mul N0
  convert hmul using 1
  ring

set_option linter.unusedVariables false in
/-- At the half-life `log 2 / λ`, half the initial inventory remains. -/
theorem decay_halfLife_value (lam N0 : ℝ) (hlam : 0 < lam) (hN0 : 0 < N0) :
    N0 * Real.exp (-lam * (Real.log 2 / lam)) = N0 / 2 := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have harg : -lam * (Real.log 2 / lam) = -Real.log 2 := by
    field_simp
  rw [harg, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  ring

set_option linter.unusedVariables false in
/-- The positive half-life is unique: any `t ≥ 0` with `N(t) = N0/2`
equals `log 2 / λ`. -/
theorem decay_halfLife_unique (lam N0 t : ℝ) (hlam : 0 < lam) (hN0 : 0 < N0)
    (ht : 0 ≤ t) (h : N0 * Real.exp (-lam * t) = N0 / 2) :
    t = Real.log 2 / lam := by
  have hN0' : N0 ≠ 0 := ne_of_gt hN0
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h2 : N0 * Real.exp (-lam * t) = N0 * (1 / 2) := by
    rw [h]
    ring
  have hexp : Real.exp (-lam * t) = 1 / 2 := mul_left_cancel₀ hN0' h2
  have hexp2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have harg : -lam * t = -Real.log 2 := Real.exp_injective (hexp.trans hexp2.symm)
  have hlamt : lam * t = Real.log 2 := by linarith
  rw [eq_div_iff hlam']
  linarith

end EarthScience
