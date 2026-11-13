/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum

/-!
# Concordia parametrization: injective on nonnegative time

For two positive distinct decay constants, the ideal closed-system
concordia point at time `t` is
`(exp (l1 * t) - 1, exp (l2 * t) - 1)`.

## i. Overview

Each coordinate is strictly increasing on nonnegative time, because the
exponential is strictly increasing and each decay constant is positive.
Hence the pair parametrization is injective on nonnegative time: two
times with the same concordia point agree in their first coordinate, and
the first coordinate alone already determines the time. The distinctness
hypothesis `l1 ≠ l2` is part of the concordia statement (it is what makes
the curve a genuine curve rather than the diagonal); the injectivity
argument itself uses only the first coordinate. Time is recovered from
the first coordinate by the logarithm: `t = log (x + 1) / l1`.

## ii. Key results

- `EarthScience.concordiaPoint`: the concordia parametrization.
- `EarthScience.concordia_first_strictMonoOn`,
  `EarthScience.concordia_second_strictMonoOn`: each coordinate is strictly
  increasing on nonnegative time.
- `EarthScience.concordia_injectiveOn`: the parametrization is injective
  on nonnegative time.
- `EarthScience.concordia_recover_time`: time recovered from the first
  coordinate.

## iii. References

- `Real.exp_lt_exp` for strict monotonicity of the exponential.
- `StrictMonoOn.injOn` for injectivity from strict monotonicity.
- `Real.log_exp` for the logarithmic recovery of time.
-/

@[expose] public section

namespace EarthScience

/-- Ideal closed-system concordia point at time `t` for decay constants
`l1, l2`: `(exp (l1 * t) - 1, exp (l2 * t) - 1)`. -/
noncomputable def concordiaPoint (l1 l2 t : ℝ) : ℝ × ℝ :=
  (Real.exp (l1 * t) - 1, Real.exp (l2 * t) - 1)

/-- The first concordia coordinate is strictly increasing on nonnegative time. -/
theorem concordia_first_strictMonoOn {l1 l2 : ℝ} (h1 : 0 < l1) :
    StrictMonoOn (fun t => (concordiaPoint l1 l2 t).1) (Set.Ici 0) := by
  intro a _ b _ hab
  simp only [concordiaPoint]
  change Real.exp (l1 * a) - 1 < Real.exp (l1 * b) - 1
  have h : l1 * a < l1 * b := mul_lt_mul_of_pos_left hab h1
  have he : Real.exp (l1 * a) < Real.exp (l1 * b) := Real.exp_lt_exp.mpr h
  exact sub_lt_sub_right he 1

/-- The second concordia coordinate is strictly increasing on nonnegative time. -/
theorem concordia_second_strictMonoOn {l1 l2 : ℝ} (h2 : 0 < l2) :
    StrictMonoOn (fun t => (concordiaPoint l1 l2 t).2) (Set.Ici 0) := by
  intro a _ b _ hab
  simp only [concordiaPoint]
  change Real.exp (l2 * a) - 1 < Real.exp (l2 * b) - 1
  have h : l2 * a < l2 * b := mul_lt_mul_of_pos_left hab h2
  have he : Real.exp (l2 * a) < Real.exp (l2 * b) := Real.exp_lt_exp.mpr h
  exact sub_lt_sub_right he 1

set_option linter.unusedVariables false in
/-- Two positive distinct decay constants define an injective concordia
parametrization on nonnegative time. -/
theorem concordia_injectiveOn {l1 l2 : ℝ} (h1 : 0 < l1) (h2 : 0 < l2)
    (hne : l1 ≠ l2) :
    Set.InjOn (concordiaPoint l1 l2) (Set.Ici 0) := by
  have hmono : StrictMonoOn (fun t => (concordiaPoint l1 l2 t).1) (Set.Ici 0) :=
    concordia_first_strictMonoOn h1
  have hinj := hmono.injOn
  intro a ha b hb hab
  apply hinj ha hb
  exact congrArg Prod.fst hab

/-- Time is recovered from the first concordia coordinate by the logarithm. -/
theorem concordia_recover_time {l1 l2 : ℝ} (h1 : 0 < l1) (t : ℝ) :
    Real.log ((concordiaPoint l1 l2 t).1 + 1) / l1 = t := by
  have h : (concordiaPoint l1 l2 t).1 + 1 = Real.exp (l1 * t) := by
    simp [concordiaPoint]
  rw [h, Real.log_exp]
  exact mul_div_cancel_left₀ t (ne_of_gt h1)

end EarthScience
