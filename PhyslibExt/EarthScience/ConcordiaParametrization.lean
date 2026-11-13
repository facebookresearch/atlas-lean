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

For decay constants `l1`, `l2`, the ideal closed-system concordia point
at age `t` is `(exp (l1 * t) - 1, exp (l2 * t) - 1)`.

## i. Overview

This is the concordia curve of the U–Pb concordia diagram (Wetherill
1956). A closed system of age `t`, the time since it closed to U and
Pb, has radiogenic-daughter/parent atomic ratios
`²⁰⁷Pb*/²³⁵U = exp (λ₂₃₅ t) - 1` and `²⁰⁶Pb*/²³⁸U = exp (λ₂₃₈ t) - 1`,
where `λ₂₃₅` and `λ₂₃₈` are the decay constants of `²³⁵U` and `²³⁸U`.
In the diagram the abscissa is `²⁰⁷Pb*/²³⁵U` and the ordinate is
`²⁰⁶Pb*/²³⁸U`, so `concordiaPoint l1 l2 t` is the concordia point at age
`t` with `l1 = λ₂₃₅` and `l2 = λ₂₃₈`. These decay constants are positive
and distinct: the conventional values are
`λ₂₃₅ = 9.8485 × 10⁻¹⁰ yr⁻¹` and `λ₂₃₈ = 1.55125 × 10⁻¹⁰ yr⁻¹`
(Steiger and Jäger 1977). The results below are stated for general real
decay constants under the sign hypotheses each one needs.

Each coordinate is strictly increasing on nonnegative time when its
decay constant is positive, because the exponential is strictly
increasing. Hence the parametrization is injective on nonnegative time
as soon as `l1 > 0`: two times with the same concordia point agree in
their first coordinate, and the first coordinate alone determines the
time (`concordia_injectiveOn_of_first_pos`). The U–Pb setting adds
`l2 > 0` and `l1 ≠ l2` (distinctness is what makes the curve differ
from the diagonal); `concordia_injectiveOn` states injectivity under
these physical-domain hypotheses, which the argument does not need.
Time is recovered from the first coordinate by the logarithm:
`t = log (x + 1) / l1`.

## ii. Key results

- `EarthScience.concordiaPoint`: the concordia parametrization.
- `EarthScience.concordia_first_strictMonoOn`,
  `EarthScience.concordia_second_strictMonoOn`: each coordinate is strictly
  increasing on nonnegative time.
- `EarthScience.concordia_injectiveOn_of_first_pos`: the parametrization
  is injective on nonnegative time whenever `l1 > 0`.
- `EarthScience.concordia_injectiveOn`: injectivity for two positive
  distinct decay constants (the U–Pb setting).
- `EarthScience.concordia_recover_time`: time recovered from the first
  coordinate.

## iii. References

- G. W. Wetherill, *Discordant uranium-lead ages, I*, Transactions,
  American Geophysical Union 37 (1956), 320–326: the concordia curve of
  `²⁰⁶Pb*/²³⁸U` against `²⁰⁷Pb*/²³⁵U` for closed U–Pb systems.
- R. H. Steiger and E. Jäger, *Subcommission on geochronology: Convention
  on the use of decay constants in geo- and cosmochronology*, Earth and
  Planetary Science Letters 36 (1977), 359–362: the conventional values of
  `λ₂₃₅` and `λ₂₃₈`.
- `Real.exp_lt_exp` for strict monotonicity of the exponential.
- `StrictMonoOn.injOn` for injectivity from strict monotonicity.
- `Real.log_exp` for the logarithmic recovery of time.
-/

@[expose] public section

namespace EarthScience

/-- Ideal closed-system concordia point at age `t` for decay constants
`l1, l2`: `(exp (l1 * t) - 1, exp (l2 * t) - 1)`. In the U–Pb concordia
diagram, `l1 = λ₂₃₅` and the first coordinate is `²⁰⁷Pb*/²³⁵U`, and
`l2 = λ₂₃₈` and the second coordinate is `²⁰⁶Pb*/²³⁸U`. -/
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

/-- The concordia parametrization is injective on nonnegative time whenever
the first decay constant is positive: the first coordinate alone determines
the time. Nothing is assumed about `l2`. -/
theorem concordia_injectiveOn_of_first_pos {l1 l2 : ℝ} (h1 : 0 < l1) :
    Set.InjOn (concordiaPoint l1 l2) (Set.Ici 0) := by
  have hmono : StrictMonoOn (fun t => (concordiaPoint l1 l2 t).1) (Set.Ici 0) :=
    concordia_first_strictMonoOn h1
  have hinj := hmono.injOn
  intro a ha b hb hab
  apply hinj ha hb
  exact congrArg Prod.fst hab

/-- Two positive distinct decay constants (the U–Pb setting `l1 = λ₂₃₅`,
`l2 = λ₂₃₈`) define an injective concordia parametrization on nonnegative
time. This is `concordia_injectiveOn_of_first_pos` on the physical domain:
only `0 < l1` enters the proof, and `0 < l2` and `l1 ≠ l2` state the
setting. -/
theorem concordia_injectiveOn {l1 l2 : ℝ} (h1 : 0 < l1) (_h2 : 0 < l2)
    (_hne : l1 ≠ l2) :
    Set.InjOn (concordiaPoint l1 l2) (Set.Ici 0) :=
  concordia_injectiveOn_of_first_pos h1

/-- Time is recovered from the first concordia coordinate by the logarithm. -/
theorem concordia_recover_time {l1 l2 : ℝ} (h1 : 0 < l1) (t : ℝ) :
    Real.log ((concordiaPoint l1 l2 t).1 + 1) / l1 = t := by
  have h : (concordiaPoint l1 l2 t).1 + 1 = Real.exp (l1 * t) := by
    simp [concordiaPoint]
  rw [h, Real.log_exp]
  exact mul_div_cancel_left₀ t (ne_of_gt h1)

end EarthScience
