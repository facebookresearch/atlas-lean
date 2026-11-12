/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Tactic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Ideal carbonate speciation and alkalinity closure

Closed carbonate-plus-water system: with `Z = h^2 + K1 * h + K1 * K2`,
the three dissolved inorganic carbon species
`C0 * h^2 / Z`, `C0 * K1 * h / Z`, `C0 * K1 * K2 / Z` sum to the total
`C0`, and the alkalinity
`A(h) = C0 * (K1 * h + 2 * K1 * K2) / Z + Kw / h - h` is strictly
decreasing on `h > 0` with exactly one root `A(h) = A0` for every real `A0`.

## i. Overview

Speciation is mass closure: the three fractions are `h^2 / Z`,
`K1 * h / Z`, `K1 * K2 / Z`, whose numerators sum to `Z`. Alkalinity
decreases because the carbonate part has negative derivative, `Kw / h`
decreases, and `-h` decreases; the root exists because `A(h) -> +infinity`
as `h -> 0+` (the `Kw / h` term dominates) and `A(h) -> -infinity` as
`h -> infinity` (the `-h` term dominates), with continuity on every
compact subinterval of `h > 0` and the intermediate value theorem.
Uniqueness follows from strict decrease. This is the ideal
closed-carbonate-plus-water model only: no borate, phosphate,
salinity/activity corrections, or precipitation. All concentrations and
equilibrium constants use one standard-concentration normalization.

## ii. Key results

- `EarthScience.carbonate_species_sum`: the three species sum to `C0`.
- `EarthScience.alkalinity_strictAntiOn`: alkalinity is strictly
  decreasing on `h > 0`.
- `EarthScience.alkalinity_unique_root`: exactly one `h > 0` with
  `A(h) = A0`, for every real `A0`.

## iii. Table of contents

- A. Speciation mass closure
- B. Alkalinity monotonicity
- C. Existence and uniqueness of the root

## iv. References

- `intermediate_value_Ioo'` in Mathlib (intermediate value theorem).
-/

@[expose] public section

namespace EarthScience


/-- Carbonate speciation: with `Z = h^2 + K1 * h + K1 * K2`, the three
species concentrations `C0 * h^2 / Z`, `C0 * K1 * h / Z`,
`C0 * K1 * K2 / Z` sum to the total dissolved inorganic carbon `C0`. -/
theorem carbonate_species_sum (C0 K1 K2 h : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2)
    (hh : 0 < h) :
    C0 * h ^ 2 / (h ^ 2 + K1 * h + K1 * K2) +
      C0 * K1 * h / (h ^ 2 + K1 * h + K1 * K2) +
      C0 * K1 * K2 / (h ^ 2 + K1 * h + K1 * K2) = C0 := by
  have hZ : (h ^ 2 + K1 * h + K1 * K2 : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < h ^ 2 + K1 * h + K1 * K2 := by positivity
    exact ne_of_gt hpos
  field_simp

/-- Alkalinity `A(h) = C0 * (K1 * h + 2 * K1 * K2) / Z + Kw / h - h` is
strictly decreasing on `h > 0` in the ideal closed-carbonate-plus-water
model. -/
theorem alkalinity_strictAntiOn (C0 K1 K2 Kw : ℝ) (hC0 : 0 ≤ C0) (hK1 : 0 < K1)
    (hK2 : 0 < K2) (hKw : 0 < Kw) :
    StrictAntiOn (fun h => C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2)
      + Kw / h - h) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hZa : (0 : ℝ) < a ^ 2 + K1 * a + K1 * K2 := by positivity
  have hZb : (0 : ℝ) < b ^ 2 + K1 * b + K1 * K2 := by positivity
  have hZa_ne : (a ^ 2 + K1 * a + K1 * K2 : ℝ) ≠ 0 := ne_of_gt hZa
  have hZb_ne : (b ^ 2 + K1 * b + K1 * K2 : ℝ) ≠ 0 := ne_of_gt hZb
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hS : (0 : ℝ) < a * b + 2 * K2 * (a + b) + K1 * K2 := by positivity
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hdiff : (K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2)
      - (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2)
      = K1 * (b - a) * (a * b + 2 * K2 * (a + b) + K1 * K2)
        / ((a ^ 2 + K1 * a + K1 * K2) * (b ^ 2 + K1 * b + K1 * K2)) := by
    field_simp
    ring
  have hKw_eq : Kw / a - Kw / b = Kw * (b - a) / (a * b) := by
    field_simp
  have hg_pos : (0 : ℝ) < K1 * (b - a) * (a * b + 2 * K2 * (a + b) + K1 * K2)
      / ((a ^ 2 + K1 * a + K1 * K2) * (b ^ 2 + K1 * b + K1 * K2)) :=
    div_pos (mul_pos (mul_pos hK1 hba) hS) (mul_pos hZa hZb)
  have hC0g : (0 : ℝ) ≤ C0 * ((K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2)
      - (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2)) := by
    rw [hdiff]
    exact mul_nonneg hC0 (le_of_lt hg_pos)
  have hKw_pos : (0 : ℝ) < Kw * (b - a) / (a * b) :=
    div_pos (mul_pos hKw hba) (mul_pos ha hb)
  have hdecomp : (C0 * (K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2) + Kw / a - a)
      - (C0 * (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2) + Kw / b - b)
      = C0 * ((K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2)
        - (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2))
        + (Kw / a - Kw / b) + (b - a) := by
    ring
  have hpos : (0 : ℝ) < C0 * ((K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2)
      - (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2))
      + (Kw / a - Kw / b) + (b - a) := by
    rw [hKw_eq]
    linarith [hC0g, hKw_pos, hba]
  change C0 * (K1 * b + 2 * K1 * K2) / (b ^ 2 + K1 * b + K1 * K2) + Kw / b - b
      < C0 * (K1 * a + 2 * K1 * K2) / (a ^ 2 + K1 * a + K1 * K2) + Kw / a - a
  linarith [hdecomp, hpos]

/-- For every real `A0` there is exactly one `h > 0` with `A(h) = A0`. -/
theorem alkalinity_unique_root (C0 K1 K2 Kw A0 : ℝ) (hC0 : 0 ≤ C0) (hK1 : 0 < K1)
    (hK2 : 0 < K2) (hKw : 0 < Kw) :
    ∃! h, 0 < h ∧
      C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2) + Kw / h - h = A0 := by
  have hAnti := alkalinity_strictAntiOn C0 K1 K2 Kw hC0 hK1 hK2 hKw
  have hInj := hAnti.injOn
  have hcarb_nonneg : ∀ h : ℝ, 0 < h →
      (0 : ℝ) ≤ C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2) := by
    intro h hh
    have hZ : (0 : ℝ) < h ^ 2 + K1 * h + K1 * K2 := by positivity
    have hnum : (0 : ℝ) ≤ K1 * h + 2 * K1 * K2 := by positivity
    exact div_nonneg (mul_nonneg hC0 hnum) (le_of_lt hZ)
  have hcarb_le : ∀ h : ℝ, 0 < h →
      C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2) ≤ 2 * C0 := by
    intro h hh
    have hZ : (0 : ℝ) < h ^ 2 + K1 * h + K1 * K2 := by positivity
    have hg : (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2) ≤ 2 := by
      rw [div_le_iff₀ hZ]
      have hnn : (0 : ℝ) ≤ 2 * h ^ 2 + K1 * h := by positivity
      linarith
    calc C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2)
        = C0 * ((K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2)) := by ring
      _ ≤ C0 * 2 := mul_le_mul_of_nonneg_left hg hC0
      _ = 2 * C0 := by ring
  have hcontinuous : ∀ lo hi : ℝ, 0 < lo → ContinuousOn
      (fun h => C0 * (K1 * h + 2 * K1 * K2) / (h ^ 2 + K1 * h + K1 * K2)
        + Kw / h - h) (Set.Icc lo hi) := by
    intro lo hi hlo
    refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) continuousOn_id
    · refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo hx.1
        have hZ : (0 : ℝ) < x ^ 2 + K1 * x + K1 * K2 := by positivity
        exact ne_of_gt hZ
    · refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const
      · exact continuousOn_id
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo hx.1
        exact ne_of_gt hx0
  set D : ℝ := |A0| + 2 * C0 + 2 with hD
  have hD_pos : (0 : ℝ) < D := by
    have h1 : (0 : ℝ) ≤ |A0| + 2 * C0 := by positivity
    rw [hD]
    linarith
  set lo : ℝ := min 1 (Kw / D) with hlo_def
  have hlo_pos : (0 : ℝ) < lo := by
    rw [hlo_def]
    exact lt_min zero_lt_one (div_pos hKw hD_pos)
  have hlo_le1 : lo ≤ 1 := by
    rw [hlo_def]
    exact min_le_left _ _
  have hlo_le : lo ≤ Kw / D := by
    rw [hlo_def]
    exact min_le_right _ _
  have hKw_lo : D ≤ Kw / lo := by
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    rw [le_div_iff₀ hlo_pos]
    have h1 : D * lo ≤ D * (Kw / D) :=
      mul_le_mul_of_nonneg_left hlo_le (le_of_lt hD_pos)
    have hDKw : D * (Kw / D) = Kw := by
      rw [mul_comm D (Kw / D)]
      exact div_mul_cancel₀ Kw hD_ne
    linarith
  have hf_lo : A0 < C0 * (K1 * lo + 2 * K1 * K2) / (lo ^ 2 + K1 * lo + K1 * K2)
      + Kw / lo - lo := by
    have h1 := hcarb_nonneg lo hlo_pos
    have h3 : A0 ≤ |A0| := le_abs_self A0
    have h4 : (0 : ℝ) ≤ 2 * C0 + 1 := by positivity
    linarith [hKw_lo, hD, hlo_le1, h1, h3, h4]
  set hi : ℝ := max 2 (2 * C0 + Kw - A0 + 1) with hhi_def
  have hhi_ge2 : 2 ≤ hi := by
    rw [hhi_def]
    exact le_max_left _ _
  have hhi_ge : 2 * C0 + Kw - A0 + 1 ≤ hi := by
    rw [hhi_def]
    exact le_max_right _ _
  have hhi_pos : (0 : ℝ) < hi := by linarith [hhi_ge2]
  have hKw_hi : Kw / hi ≤ Kw := by
    have h1 : (1 : ℝ) ≤ hi := by linarith [hhi_ge2]
    rw [div_le_iff₀ hhi_pos]
    have h2 : Kw * 1 ≤ Kw * hi := mul_le_mul_of_nonneg_left h1 (le_of_lt hKw)
    linarith
  have hf_hi : C0 * (K1 * hi + 2 * K1 * K2) / (hi ^ 2 + K1 * hi + K1 * K2)
      + Kw / hi - hi < A0 := by
    have h1 := hcarb_le hi hhi_pos
    linarith [hKw_hi, hhi_ge, h1]
  have hlo_lt_hi : lo < hi :=
    lt_of_le_of_lt hlo_le1 (lt_of_lt_of_le (by norm_num) hhi_ge2)
  have hcont := hcontinuous lo hi hlo_pos
  have hsub := intermediate_value_Ioo' (le_of_lt hlo_lt_hi) hcont
  obtain ⟨c, hc_mem, hfc⟩ := hsub ⟨hf_hi, hf_lo⟩
  have hc_pos : (0 : ℝ) < c := lt_trans hlo_pos hc_mem.1
  dsimp only at hfc
  refine ⟨c, ⟨hc_pos, hfc⟩, ?_⟩
  intro y hy
  obtain ⟨hy0, hyEq⟩ := hy
  apply hInj (Set.mem_Ioi.mpr hy0) (Set.mem_Ioi.mpr hc_pos)
  change C0 * (K1 * y + 2 * K1 * K2) / (y ^ 2 + K1 * y + K1 * K2) + Kw / y - y
      = C0 * (K1 * c + 2 * K1 * K2) / (c ^ 2 + K1 * c + K1 * K2) + Kw / c - c
  rw [hyEq, hfc]

end EarthScience
