/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ConductiveDissipation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory intervalIntegral

/-!
# Conductive-dissipation checks

Concrete consumers of `PhyslibExt.EarthScience.ConductiveDissipation`:
conductivity `k = 2` and the linear profile `T z = 3 * z`, whose
derivative is `3` everywhere. The dissipation density is
`2 * 3 ^ 2 = 18` and the integrated dissipation over `[0, 1]` is `18`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
concrete case shows the dissipation is strictly positive, not merely
nonnegative, and the `k = 0` boundary gives dissipation `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear profile, positive conductivity
- B. Zero-conductivity boundary

## iv. References

- `PhyslibExt.EarthScience.ConductiveDissipation`
-/

/-- Public shape of the conductive-dissipation theorem. -/
example {k : ℝ} (hk : 0 ≤ k) {T : ℝ → ℝ} {a b z : ℝ} (hab : a ≤ b)
    (hInt : IntervalIntegrable (fun z => k * (deriv T z) ^ 2) volume a b) :
    0 ≤ k * (deriv T z) ^ 2 ∧
    0 ≤ ∫ z in a..b, k * (deriv T z) ^ 2 :=
  EarthScience.conductive_dissipation_nonneg hk hab hInt

/-- Derivative of the linear profile `T z = 3 * z` is `3`. -/
private lemma deriv_linear_three (z : ℝ) : deriv (fun z : ℝ => 3 * z) z = 3 := by
  have h : HasDerivAt (fun z : ℝ => 3 * z) 3 z := by
    simpa using (hasDerivAt_id z).const_mul (3 : ℝ)
  exact h.deriv

/-- Integrability of the dissipation integrand for `k = 2`, `T z = 3 * z`. -/
private lemma dissipation_integrable :
    IntervalIntegrable (fun z => (2 : ℝ) * (deriv (fun z => 3 * z) z) ^ 2)
      volume (0 : ℝ) 1 := by
  have hfun : (fun z => (2 : ℝ) * (deriv (fun z => 3 * z) z) ^ 2)
      = fun _ => (18 : ℝ) := by
    funext z
    rw [deriv_linear_three]
    norm_num
  rw [hfun]
  exact intervalIntegrable_const

/-- Concrete case: dissipation density `2 * 3 ^ 2 = 18 ≥ 0`. -/
example : 0 ≤ (2 : ℝ) * (deriv (fun z : ℝ => 3 * z) (1 : ℝ)) ^ 2 :=
  (EarthScience.conductive_dissipation_nonneg (k := (2 : ℝ))
    (T := fun z : ℝ => 3 * z) (a := 0) (b := 1) (z := 1) (hk := by norm_num)
    (hab := by norm_num) (hInt := dissipation_integrable)).1

/-- Concrete case: integrated dissipation over `[0, 1]` is exactly `18`. -/
example : ∫ z in (0 : ℝ)..1, (2 : ℝ) * (deriv (fun z : ℝ => 3 * z) z) ^ 2 = 18 := by
  have hfun : (fun z => (2 : ℝ) * (deriv (fun z => 3 * z) z) ^ 2)
      = fun _ => (18 : ℝ) := by
    funext z
    rw [deriv_linear_three]
    norm_num
  rw [hfun, intervalIntegral.integral_const]
  norm_num

/-- Zero-conductivity boundary: dissipation is `0`. -/
example (T : ℝ → ℝ) (z : ℝ) :
    (0 : ℝ) * (deriv T z) ^ 2 = 0 := by
  simp
