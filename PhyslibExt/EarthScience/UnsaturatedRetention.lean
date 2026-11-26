/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Unsaturated retention: van Genuchten effective saturation

For gauge pressure head `h ≤ 0`, `α > 0` and `n > 1`, the van Genuchten
effective saturation with the Mualem exponent `m = 1 - 1 / n` lies in
`(0, 1]`, equals `1` at zero head, and is strictly below `1` at every
finite negative head.

## i. Overview

The effective saturation is `S_e = (θ - θ_r) / (θ_s - θ_r)`, represented
here only through its closed form
`S_e(h) = (1 + (α |h|)^n)^(-(1 - 1 / n))`. Here `h` is the gauge pressure
head in units of length, with `h ≤ 0` on the unsaturated branch; the
positive head in the source equation is `|h| = -h`. The parameter
`α > 0` has units of inverse length, so `α * |h|` is dimensionless, and
`n > 1` is dimensionless. Powers are real powers (`Real.rpow`); on the
locked domain the inner base is nonnegative and the outer base is at
least `1`, so no negative-base branch or totalized value is used in the
range statement.

The scope is the closed-form saturation, its range, the bridge to the
source form, the zero-head value, the strict bound at a finite negative
head, two controls on the exponent restriction, and the volumetric
water-content reading `θ = θ_r + (θ_s - θ_r) * S_e` of Eq. [2]: its
bounds `θ_r < θ ≤ θ_s` on the unsaturated branch and the `θ_s ≤ θ_r`
control. No hydraulic conductivity, Richards equation, hysteresis model,
calibrated parameter, dry-limit statement, or saturated-branch extension
(`h > 0`) is included. No separate water-content definition is
introduced; `θ` is written inline as above.

## ii. Key results

- `EarthScience.vanGenuchtenSe`: the closed-form effective saturation.
- `EarthScience.vanGenuchtenSe_pos_and_le_one`: the range `(0, 1]` on the
  unsaturated branch.
- `EarthScience.vanGenuchtenSe_eq_source`: the gauge-head form equals the
  source form with positive head `-h`.
- `EarthScience.vanGenuchtenSe_zero_head` and
  `EarthScience.vanGenuchtenSe_lt_one`: the endpoint value and the strict
  bound at negative head.
- `EarthScience.vanGenuchtenSe_exponent_one` and
  `EarthScience.one_lt_vanGenuchtenSe_of_lt_one`: endpoint controls. At
  `n = 1` the saturation is identically `1`, so the range endpoint still
  holds but the strict unsaturated bound fails; for `0 < n < 1` the upper
  bound `S_e ≤ 1` itself fails.
- `EarthScience.vanGenuchtenSe_eq_div_iff_waterContent`: the Eq. [2]
  bridge between effective saturation and water content.
- `EarthScience.vanGenuchten_waterContent_mem_Ioc`: the water content
  lies in `(θ_r, θ_s]`.
- `EarthScience.vanGenuchten_waterContent_le_residual_of_le`: for
  `θ_s ≤ θ_r` the water content is at most `θ_r`.

## iii. Table of contents

- A. Effective saturation and range
- B. Volumetric water content

## iv. References

- M. Th. van Genuchten, "A closed-form equation for predicting the
  hydraulic conductivity of unsaturated soils", *Soil Sci. Soc. Am. J.*
  44 (1980), 892-898: Eq. [2]-[3] on p. 892; `k = m - 1 + 1 / n = 0`
  with Eq. [7]-[8] on p. 893; Eq. [21]-[22] on p. 894.

## A. Effective saturation and range
-/

@[expose] public section

namespace EarthScience

/-- van Genuchten (1980) effective saturation with the Mualem exponent
`m = 1 - 1/n`, in gauge-head form: `S_e(h) = (1 + (α |h|)^n)^(-(1 - 1/n))`.
Real powers throughout. Physically meaningful only for `α > 0`, `n > 1`,
`h ≤ 0`; outside that domain the expression is a totalized value, with
`1 / 0 = 0` (so `S_e = 1 / 2` at `n = 0`, as `x ^ 0 = 1`), `0 ^ y = 0` for
`y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for `x < 0`. -/
noncomputable def vanGenuchtenSe (α n h : ℝ) : ℝ :=
  (1 + (α * |h|) ^ n) ^ (-(1 - 1 / n))

private lemma one_lt_one_add_rpow_base {α n h : ℝ} (hα : 0 < α)
    (hh : h < 0) : (1 : ℝ) < 1 + (α * |h|) ^ n := by
  have hah : (0 : ℝ) < α * |h| := mul_pos hα (abs_pos.mpr (ne_of_lt hh))
  have hpow : (0 : ℝ) < (α * |h|) ^ n := Real.rpow_pos_of_pos hah n
  linarith

/-- Retention saturation range: on the unsaturated branch `h ≤ 0`, with
`α > 0` and `n > 1`, the van Genuchten effective saturation lies in `(0, 1]`.
No claim is made for `h > 0`. The hypothesis `hh` records the locked
unsaturated domain; the formula depends on `h` only through `|h|`, so `hh`
is a domain hypothesis rather than an algebraic one. -/
theorem vanGenuchtenSe_pos_and_le_one {α n h : ℝ} (hα : 0 < α) (hn : 1 < n)
    (hh : h ≤ 0) :
    0 < vanGenuchtenSe α n h ∧ vanGenuchtenSe α n h ≤ 1 := by
  have hn_pos : (0 : ℝ) < n := lt_trans zero_lt_one hn
  have h1n : 1 / n < 1 := (div_lt_one hn_pos).mpr hn
  have hexp : -(1 - 1 / n) ≤ 0 := by linarith
  have habs : |h| = -h := abs_of_nonpos hh
  have hbase : (1 : ℝ) ≤ 1 + (α * -h) ^ n := by
    have hpow : (0 : ℝ) ≤ (α * -h) ^ n :=
      Real.rpow_nonneg (mul_nonneg hα.le (neg_nonneg.mpr hh)) n
    linarith
  have hpos : (0 : ℝ) < 1 + (α * -h) ^ n := lt_of_lt_of_le zero_lt_one hbase
  unfold vanGenuchtenSe
  rw [habs]
  exact ⟨Real.rpow_pos_of_pos hpos _, Real.rpow_le_one_of_one_le_of_nonpos hbase hexp⟩

/-- Source bridge: for `α > 0`, `n > 1`, and `h ≤ 0`, the gauge-head form
equals Eq. [3] of van Genuchten (1980), `[1 / (1 + (α h_p)^n)]^m` with the
paper's positive head `h_p = -h` and `m = 1 - 1/n`. The premise `n > 1` is
the source exponent domain; outside it the displayed expressions are only
totalized values. -/
theorem vanGenuchtenSe_eq_source {α n h : ℝ} (hα : 0 < α) (_hn : 1 < n)
    (hh : h ≤ 0) :
    vanGenuchtenSe α n h = (1 / (1 + (α * -h) ^ n)) ^ (1 - 1 / n) := by
  have habs : |h| = -h := abs_of_nonpos hh
  have hB0 : (0 : ℝ) ≤ 1 + (α * -h) ^ n := by
    have hpow : (0 : ℝ) ≤ (α * -h) ^ n :=
      Real.rpow_nonneg (mul_nonneg hα.le (neg_nonneg.mpr hh)) n
    linarith
  unfold vanGenuchtenSe
  rw [habs, Real.div_rpow zero_le_one hB0, Real.one_rpow, Real.rpow_neg hB0]
  exact (one_div _).symm

/-- Zero head is saturated: at `h = 0`, `S_e = 1` whenever `n > 1`
(any `α`, since `α * |0| = 0`). -/
lemma vanGenuchtenSe_zero_head {α n : ℝ} (hn : 1 < n) :
    vanGenuchtenSe α n 0 = 1 := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_trans zero_lt_one hn)
  unfold vanGenuchtenSe
  rw [abs_zero, mul_zero, Real.zero_rpow hn0, add_zero, Real.one_rpow]

/-- A finite negative head is strictly unsaturated: for `α > 0`, `n > 1` and
`h < 0`, `S_e < 1`. -/
lemma vanGenuchtenSe_lt_one {α n h : ℝ} (hα : 0 < α) (hn : 1 < n)
    (hh : h < 0) :
    vanGenuchtenSe α n h < 1 := by
  have hn_pos : (0 : ℝ) < n := lt_trans zero_lt_one hn
  have h1n : 1 / n < 1 := (div_lt_one hn_pos).mpr hn
  have hexp : -(1 - 1 / n) < 0 := by linarith
  have hbase : (1 : ℝ) < 1 + (α * |h|) ^ n :=
    one_lt_one_add_rpow_base hα hh
  unfold vanGenuchtenSe
  exact Real.rpow_lt_one_of_one_lt_of_neg hbase hexp

/-- Control, `n = 1`: for all real `α` and `h` the Mualem exponent vanishes and `S_e ≡ 1`, so the
retention curve degenerates and the strict unsaturated bound fails. The value `1` uses `x ^ 0 = 1`
for every real `x`, so it also holds where the base `1 + α * |h|` is `0` or negative, which happens
for some `h` when `α < 0`. -/
lemma vanGenuchtenSe_exponent_one (α h : ℝ) :
    vanGenuchtenSe α 1 h = 1 := by
  have he : (-(1 - 1 / (1 : ℝ)) : ℝ) = 0 := by norm_num
  unfold vanGenuchtenSe
  rw [he, Real.rpow_zero]

/-- Control, `α > 0` and `0 < n < 1`: the exponent `-(1 - 1/n)` is positive and the upper
bound fails at every finite negative head, so `n > 1` cannot be dropped from
the range statement. -/
lemma one_lt_vanGenuchtenSe_of_lt_one {α n h : ℝ} (hα : 0 < α) (hn₀ : 0 < n)
    (hn : n < 1) (hh : h < 0) :
    1 < vanGenuchtenSe α n h := by
  have h1n : (1 : ℝ) < 1 / n := one_lt_one_div hn₀ hn
  have hexp : (0 : ℝ) < -(1 - 1 / n) := by linarith
  have hbase : (1 : ℝ) < 1 + (α * |h|) ^ n :=
    one_lt_one_add_rpow_base hα hh
  unfold vanGenuchtenSe
  exact Real.one_lt_rpow hbase hexp

/-! ## B. Volumetric water content -/

/-- Eq. [2] bridge (van Genuchten (1980), Eq. [2] on p. 892; the
water-content form is Eq. [21] with [22] on p. 894): for residual and
saturated water contents `θr < θs`, a
water content `θ` has effective saturation `(θ - θr) / (θs - θr)` equal to the
van Genuchten value at head `h` exactly when
`θ = θr + (θs - θr) * vanGenuchtenSe α n h`. The equivalence holds for all real `θ`, `α`, `n` and
`h` and every value of `vanGenuchtenSe α n h`, including the values that its conventions
(`1 / 0 = 0`, `x ^ 0 = 1`, `0 ^ y = 0` for `y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for `x < 0`)
give outside the intended domain `α > 0`, `n > 1`, `h ≤ 0`. -/
theorem vanGenuchtenSe_eq_div_iff_waterContent {θr θs θ α n h : ℝ}
    (hθ : θr < θs) :
    (θ - θr) / (θs - θr) = vanGenuchtenSe α n h ↔
      θ = θr + (θs - θr) * vanGenuchtenSe α n h := by
  have hne : θs - θr ≠ 0 := sub_ne_zero.mpr (ne_of_gt hθ)
  rw [div_eq_iff hne]
  constructor <;> intro h <;> linear_combination h

/-- Water-content bounds: for `θr < θs`, on the unsaturated branch `h ≤ 0`
with `α > 0` and `n > 1`, the volumetric water content
`θr + (θs - θr) * S_e(h)` lies in `(θr, θs]`. -/
theorem vanGenuchten_waterContent_mem_Ioc
    {θr θs α n h : ℝ} (hθ : θr < θs) (hα : 0 < α) (hn : 1 < n) (hh : h ≤ 0) :
    θr + (θs - θr) * vanGenuchtenSe α n h ∈ Set.Ioc θr θs := by
  obtain ⟨hSe_pos, hSe_le⟩ := vanGenuchtenSe_pos_and_le_one hα hn hh
  have hd : 0 < θs - θr := sub_pos.mpr hθ
  have hmul_pos : 0 < (θs - θr) * vanGenuchtenSe α n h := mul_pos hd hSe_pos
  have hmul_le : (θs - θr) * vanGenuchtenSe α n h ≤ (θs - θr) * 1 :=
    mul_le_mul_of_nonneg_left hSe_le hd.le
  rw [mul_one] at hmul_le
  refine ⟨?_, ?_⟩ <;> linarith

/-- Control, `θs ≤ θr`: on the unsaturated branch with `α > 0` and `n > 1`,
the water content is at most `θr`, so the positive excess needs `θr < θs`. -/
lemma vanGenuchten_waterContent_le_residual_of_le
    {θr θs α n h : ℝ} (hθ : θs ≤ θr) (hα : 0 < α) (hn : 1 < n) (hh : h ≤ 0) :
    θr + (θs - θr) * vanGenuchtenSe α n h ≤ θr := by
  obtain ⟨hSe_pos, _⟩ := vanGenuchtenSe_pos_and_le_one hα hn hh
  have hmul : (θs - θr) * vanGenuchtenSe α n h ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) hSe_pos.le
  linarith

end EarthScience
