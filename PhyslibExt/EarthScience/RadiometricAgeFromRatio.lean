/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Age inversion from the daughter/parent ratio

In a closed single-step system with initial parent `P0 > 0`, no
initial daughter, parent `P(t) = P0 * exp (-λ t)` and daughter
`D(t) = P0 - P(t)`, the age recovered from the daughter/parent ratio,
`log (1 + D(t) / P(t)) / λ`, equals `t`.

## i. Overview

The model is the standard one for a radioactive parent decaying to a
stable radiogenic daughter: the system is closed (no parent or daughter
atoms enter or leave), each decay turns one parent atom into one
daughter atom, so `D(t) = P0 - P(t)`, and no daughter is present at
`t = 0`. These assumptions are encoded in the formulas for `P(t)` and
`D(t)`; they are not derived here.

The ratio is `D(t) / P(t) = exp (λ t) - 1`, so `1 + D(t) / P(t)` is
`exp (λ t)`; the logarithm inverts the exponential (`Real.log_exp`)
and division by `λ ≠ 0` recovers `t`. The ratio itself is nonnegative
for `t ≥ 0` and is `0` at `t = 0`; only `1 + D(t) / P(t) = exp (λ t)`
needs to be positive. The hypothesis `t ≥ 0` is kept as the
admissibility condition for the age even though the algebra needs only
`P0 > 0` and `λ > 0`. This is the single-system daughter/parent
inversion; `EarthScience.isochron_age_eq` inverts a two-sample
isochron slope instead.

## ii. Key results

- `EarthScience.radiometric_age_from_ratio`: the recovered age
  equals `t`.

## iii. References

- G. Faure and T. M. Mensing, *Isotopes: Principles and Applications*,
  3rd ed., John Wiley & Sons, 2005: Chapter 3 (Radioactive Decay),
  §3.1 (Law of Radioactivity), for `P(t) = P0 * exp (-λ t)`; and
  Chapter 4 (Geochronometry), §4.1 (Growth of Radiogenic Daughters) for
  the stable radiogenic daughter and the age equation obtained by
  solving `D = P * (exp (λ t) - 1)` for `t`, and §4.2 (Assumptions for
  Dating) for the closed-system and initial-daughter assumptions.
- `Real.log_exp`, `Real.exp_neg`, `Real.exp_ne_zero` (Mathlib).
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Age inversion recovers time from the daughter/parent ratio: in a
closed single-step system with initial parent `P0 > 0`, no initial
daughter, parent `P(t) = P0 * exp (-λ t)` and daughter
`D(t) = P0 - P(t)`, the age recovered from the daughter/parent ratio,
`log (1 + D(t) / P(t)) / λ`, equals `t`. For admissible ages `t ≥ 0`
the ratio is nonnegative (zero at `t = 0`), and the logarithm's
argument `1 + D(t) / P(t) = exp (λ t)` is positive. -/
theorem radiometric_age_from_ratio {lam P0 t : ℝ} (hlam : 0 < lam)
    (hP0 : 0 < P0) (ht : 0 ≤ t) :
    Real.log (1 + (P0 - P0 * Real.exp (-lam * t))
        / (P0 * Real.exp (-lam * t))) / lam = t := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hP0_ne : P0 ≠ 0 := ne_of_gt hP0
  have hE_ne : Real.exp (-lam * t) ≠ 0 := Real.exp_ne_zero _
  have hP_ne : P0 * Real.exp (-lam * t) ≠ 0 := mul_ne_zero hP0_ne hE_ne
  have harg : 1 + (P0 - P0 * Real.exp (-lam * t)) / (P0 * Real.exp (-lam * t))
      = Real.exp (lam * t) := by
    have h1 : 1 + (P0 - P0 * Real.exp (-lam * t)) / (P0 * Real.exp (-lam * t))
        = P0 / (P0 * Real.exp (-lam * t)) := by
      field_simp
      ring
    rw [h1]
    have h2 : P0 / (P0 * Real.exp (-lam * t)) = 1 / Real.exp (-lam * t) := by
      field_simp
    rw [h2]
    have hneg : -lam * t = -(lam * t) := by ring
    rw [hneg, Real.exp_neg, one_div, inv_inv]
  rw [harg, Real.log_exp]
  field_simp

end EarthScience
