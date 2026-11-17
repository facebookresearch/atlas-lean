/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Space thermal-power ports: radiator box trapping

## i. Overview

A lumped radiator model `C * T' = Q - Krad * T^4` with heat
capacity `C > 0`, radiation coefficient `Krad > 0`, and constant
heat input `Q`. On a box `[Tmin, Tmax]` with `0 ≤ Tmin ≤ Tmax`
whose ends satisfy the inward sign conditions
`Q - Krad * Tmin^4 ≥ 0 ≥ Q - Krad * Tmax^4`, solutions starting in
the box never leave it. The proof uses the globally Lipschitz
clipped field (the unrestricted quartic is not globally
Lipschitz): the clipped rate agrees with the physical rate on the
box, and a last-exit-time argument with the inward signs traps
every forward solution in the box, where it therefore solves the
original field.

## ii. Key results

- `ThermalPowerPorts.clippedRadiatorRate_lipschitz`: the clipped
  rate is globally Lipschitz with constant
  `Krad * (4 * Tmax^3) / C`.
- `ThermalPowerPorts.radiator_solution_trapped`: forward solutions
  with `HasDerivWithinAt` on `Set.Ici 0` starting in the box stay
  in the box for all `t ≥ 0`.
- `ThermalPowerPorts.radiator_solution_exists_trapped`: for every
  initial temperature in the box, the clipped field's global
  solution (global existence for globally Lipschitz fields) stays
  in the box for `t ≥ 0` and there solves the original field.

## iii. Table of contents

- A. The clipped radiator field and box trapping

## iv. References

- The model is the standard lumped Stefan-Boltzmann radiator
  balance; the statement is self-contained.

## A. The clipped radiator field and box trapping

-/

@[expose] public section

namespace ThermalPowerPorts

/-- Radiator temperature rate for heat capacity `C`, radiation
coefficient `Krad`, and constant heat input `Q`:
`rate(T) = (Q - Krad * T^4) / C`. -/
noncomputable def radiatorRate (C Krad Q T : ℝ) : ℝ :=
  (Q - Krad * T ^ 4) / C

/-- The clipped radiator rate: the rate of the temperature clipped
to the invariant box `[Tmin, Tmax]`. It agrees with the physical
rate on the box and is globally defined. -/
noncomputable def clippedRadiatorRate (C Krad Q Tmin Tmax T : ℝ) : ℝ :=
  radiatorRate C Krad Q (min (max T Tmin) Tmax)

private lemma clip_mem {Tmin Tmax T : ℝ} (hmax : Tmin ≤ Tmax) :
    min (max T Tmin) Tmax ∈ Set.Icc Tmin Tmax := by
  refine ⟨?_, ?_⟩
  · exact le_min (le_max_right T Tmin) hmax
  · exact min_le_right _ _

private lemma max_sub_max_le (x y c : ℝ) : max x c - max y c ≤ |x - y| := by
  have hxy : x ≤ y + |x - y| := by
    have h : x - y ≤ |x - y| := le_abs_self _
    linarith
  have h1 : x ≤ max (y + |x - y|) c := le_trans hxy (le_max_left _ _)
  have h2 : c ≤ max (y + |x - y|) c := le_max_right _ _
  have h3 : max x c ≤ max (y + |x - y|) c := max_le_iff.mpr ⟨h1, h2⟩
  have hd : (0 : ℝ) ≤ |x - y| := abs_nonneg _
  have h4 : y + |x - y| ≤ max y c + |x - y| := by
    have hy : y ≤ max y c := le_max_left _ _
    linarith
  have h5 : c ≤ max y c + |x - y| := by
    have hc : c ≤ max y c := le_max_right _ _
    linarith
  have h6 : max (y + |x - y|) c ≤ max y c + |x - y| := max_le_iff.mpr ⟨h4, h5⟩
  linarith

private lemma abs_max_sub_max_le (a b c : ℝ) : |max a c - max b c| ≤ |a - b| := by
  rw [abs_le]
  refine ⟨?_, max_sub_max_le a b c⟩
  have h : max b c - max a c ≤ |b - a| := max_sub_max_le b a c
  rw [abs_sub_comm] at h
  linarith

private lemma min_sub_min_le (x y c : ℝ) : min x c - min y c ≤ |x - y| := by
  have hxy : x ≤ y + |x - y| := by
    have h : x - y ≤ |x - y| := le_abs_self _
    linarith
  have h1 : min x c ≤ y + |x - y| := le_trans (min_le_left _ _) hxy
  have h2 : min x c ≤ c := min_le_right _ _
  have h3 : min x c ≤ min (y + |x - y|) c := le_min_iff.mpr ⟨h1, h2⟩
  have h6 : min (y + |x - y|) c ≤ min y c + |x - y| := by
    rw [min_le_iff]
    cases le_total y c with
    | inl hyc =>
      left
      have hmin : min y c = y := min_eq_left hyc
      linarith
    | inr hcy =>
      right
      have hmin : min y c = c := min_eq_right hcy
      have hd : (0 : ℝ) ≤ |x - y| := abs_nonneg _
      linarith
  linarith

private lemma abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  rw [abs_le]
  refine ⟨?_, min_sub_min_le a b c⟩
  have h : min b c - min a c ≤ |b - a| := min_sub_min_le b a c
  rw [abs_sub_comm] at h
  linarith

private lemma abs_clip_sub_clip_le (Tmin Tmax a b : ℝ) :
    |min (max a Tmin) Tmax - min (max b Tmin) Tmax| ≤ |a - b| :=
  le_trans (abs_min_sub_min_le _ _ _) (abs_max_sub_max_le _ _ _)

private lemma abs_pow4_sub_le (x y Tmin Tmax : ℝ) (hmin : 0 ≤ Tmin)
    (hx : x ∈ Set.Icc Tmin Tmax) (hy : y ∈ Set.Icc Tmin Tmax) :
    |x ^ 4 - y ^ 4| ≤ (4 * Tmax ^ 3) * |x - y| := by
  have ⟨hxlo, hxhi⟩ := hx
  have ⟨hylo, hyhi⟩ := hy
  have hx0 : (0 : ℝ) ≤ x := le_trans hmin hxlo
  have hy0 : (0 : ℝ) ≤ y := le_trans hmin hylo
  have hT0 : (0 : ℝ) ≤ Tmax := le_trans hmin (le_trans hxlo hxhi)
  have hx3 : x ^ 3 ≤ Tmax ^ 3 := pow_le_pow_left₀ hx0 hxhi 3
  have hy3 : y ^ 3 ≤ Tmax ^ 3 := pow_le_pow_left₀ hy0 hyhi 3
  have hx2 : x ^ 2 ≤ Tmax ^ 2 := pow_le_pow_left₀ hx0 hxhi 2
  have hy2 : y ^ 2 ≤ Tmax ^ 2 := pow_le_pow_left₀ hy0 hyhi 2
  have hT2 : (0 : ℝ) ≤ Tmax ^ 2 := pow_nonneg hT0 2
  have hy2nn : (0 : ℝ) ≤ y ^ 2 := pow_nonneg hy0 2
  have hx2y : x ^ 2 * y ≤ Tmax ^ 3 := by
    have h1 : x ^ 2 * y ≤ Tmax ^ 2 * y := mul_le_mul_of_nonneg_right hx2 hy0
    have h2 : Tmax ^ 2 * y ≤ Tmax ^ 2 * Tmax := mul_le_mul_of_nonneg_left hyhi hT2
    have h3 : Tmax ^ 2 * Tmax = Tmax ^ 3 := by ring
    calc x ^ 2 * y ≤ Tmax ^ 2 * y := h1
      _ ≤ Tmax ^ 2 * Tmax := h2
      _ = Tmax ^ 3 := h3
  have hxy2 : x * y ^ 2 ≤ Tmax ^ 3 := by
    have h1 : x * y ^ 2 ≤ Tmax * y ^ 2 := mul_le_mul_of_nonneg_right hxhi hy2nn
    have h2 : Tmax * y ^ 2 ≤ Tmax * Tmax ^ 2 := mul_le_mul_of_nonneg_left hy2 hT0
    have h3 : Tmax * Tmax ^ 2 = Tmax ^ 3 := by ring
    calc x * y ^ 2 ≤ Tmax * y ^ 2 := h1
      _ ≤ Tmax * Tmax ^ 2 := h2
      _ = Tmax ^ 3 := h3
  have nx3 : (0 : ℝ) ≤ x ^ 3 := pow_nonneg hx0 3
  have nx2y : (0 : ℝ) ≤ x ^ 2 * y := mul_nonneg (pow_nonneg hx0 2) hy0
  have nxy2 : (0 : ℝ) ≤ x * y ^ 2 := mul_nonneg hx0 (pow_nonneg hy0 2)
  have ny3 : (0 : ℝ) ≤ y ^ 3 := pow_nonneg hy0 3
  have hSnn : (0 : ℝ) ≤ x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 :=
    add_nonneg (add_nonneg (add_nonneg nx3 nx2y) nxy2) ny3
  have hSle : x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 ≤ 4 * Tmax ^ 3 := by
    linarith [hx3, hx2y, hxy2, hy3]
  have hSabs : |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3| ≤ 4 * Tmax ^ 3 := by
    rw [abs_of_nonneg hSnn]
    exact hSle
  have hfactor : x ^ 4 - y ^ 4 =
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by
    ring
  calc |x ^ 4 - y ^ 4|
      = |x - y| * |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3| := by
        rw [hfactor, abs_mul]
    _ ≤ |x - y| * (4 * Tmax ^ 3) := mul_le_mul_of_nonneg_left hSabs (abs_nonneg _)
    _ = (4 * Tmax ^ 3) * |x - y| := mul_comm _ _

/-- The clipped rate agrees with the physical rate on the box. -/
lemma clippedRadiatorRate_eq_of_mem {C Krad Q Tmin Tmax T : ℝ}
    (h : T ∈ Set.Icc Tmin Tmax) :
    clippedRadiatorRate C Krad Q Tmin Tmax T = radiatorRate C Krad Q T := by
  have ⟨hlo, hhi⟩ := h
  unfold clippedRadiatorRate
  rw [max_eq_left hlo, min_eq_left hhi]

/-- Global Lipschitz bound for the clipped rate: for `0 ≤ Tmin`,
`Tmin ≤ Tmax`, `Krad, C > 0`, with `M = max Tmax |Tmin|` (which is
`Tmax` under these hypotheses),
`|clippedRate a - clippedRate b| ≤ (Krad * (4 * Tmax^3) / C) * |a - b|`
for all real `a, b`. -/
lemma clippedRadiatorRate_lipschitz {C Krad Q Tmin Tmax : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax)
    (a b : ℝ) :
    |clippedRadiatorRate C Krad Q Tmin Tmax a -
      clippedRadiatorRate C Krad Q Tmin Tmax b| ≤
      (Krad * (4 * Tmax ^ 3) / C) * |a - b| := by
  have hu_mem : min (max a Tmin) Tmax ∈ Set.Icc Tmin Tmax := clip_mem hmax
  have hv_mem : min (max b Tmin) Tmax ∈ Set.Icc Tmin Tmax := clip_mem hmax
  have hquart : |(min (max a Tmin) Tmax) ^ 4 - (min (max b Tmin) Tmax) ^ 4| ≤
      (4 * Tmax ^ 3) * |min (max a Tmin) Tmax - min (max b Tmin) Tmax| :=
    abs_pow4_sub_le _ _ _ _ hmin hu_mem hv_mem
  have hclip : |min (max a Tmin) Tmax - min (max b Tmin) Tmax| ≤ |a - b| :=
    abs_clip_sub_clip_le _ _ _ _
  have hT0 : (0 : ℝ) ≤ Tmax := le_trans hmin hmax
  have hM : (0 : ℝ) ≤ 4 * Tmax ^ 3 := by
    have h3 : (0 : ℝ) ≤ Tmax ^ 3 := pow_nonneg hT0 3
    linarith
  have hD : |(min (max a Tmin) Tmax) ^ 4 - (min (max b Tmin) Tmax) ^ 4| ≤
      (4 * Tmax ^ 3) * |a - b| :=
    le_trans hquart (mul_le_mul_of_nonneg_left hclip hM)
  have hKC : (0 : ℝ) ≤ Krad / C := div_nonneg (le_of_lt hK) (le_of_lt hC)
  have hmul : (Krad / C) * |(min (max a Tmin) Tmax) ^ 4 - (min (max b Tmin) Tmax) ^ 4| ≤
      (Krad / C) * ((4 * Tmax ^ 3) * |a - b|) :=
    mul_le_mul_of_nonneg_left hD hKC
  unfold clippedRadiatorRate radiatorRate
  have hnum : (Q - Krad * (min (max a Tmin) Tmax) ^ 4) -
      (Q - Krad * (min (max b Tmin) Tmax) ^ 4) =
      Krad * ((min (max b Tmin) Tmax) ^ 4 - (min (max a Tmin) Tmax) ^ 4) := by
    ring
  have hdiff : (Q - Krad * (min (max a Tmin) Tmax) ^ 4) / C -
      (Q - Krad * (min (max b Tmin) Tmax) ^ 4) / C =
      Krad * ((min (max b Tmin) Tmax) ^ 4 - (min (max a Tmin) Tmax) ^ 4) / C := by
    rw [← sub_div, hnum]
  rw [hdiff, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hC,
    abs_sub_comm ((min (max b Tmin) Tmax) ^ 4) ((min (max a Tmin) Tmax) ^ 4)]
  have hLHS : Krad * |(min (max a Tmin) Tmax) ^ 4 - (min (max b Tmin) Tmax) ^ 4| / C =
      (Krad / C) * |(min (max a Tmin) Tmax) ^ 4 - (min (max b Tmin) Tmax) ^ 4| := by
    ring
  have hRHS : (Krad * (4 * Tmax ^ 3) / C) * |a - b| =
      (Krad / C) * ((4 * Tmax ^ 3) * |a - b|) := by
    ring
  rw [hLHS, hRHS]
  exact hmul

/-- Inward sign at the lower box end: `rate(Tmin) ≥ 0` whenever
`Q - Krad * Tmin^4 ≥ 0` and `C > 0`. -/
lemma radiatorRate_nonneg_at_min {C Krad Q Tmin : ℝ} (hC : 0 < C)
    (h : 0 ≤ Q - Krad * Tmin ^ 4) :
    0 ≤ radiatorRate C Krad Q Tmin := by
  unfold radiatorRate
  exact div_nonneg h (le_of_lt hC)

/-- Inward sign at the upper box end: `rate(Tmax) ≤ 0` whenever
`Q - Krad * Tmax^4 ≤ 0` and `C > 0`. -/
lemma radiatorRate_nonpos_at_max {C Krad Q Tmax : ℝ} (hC : 0 < C)
    (h : Q - Krad * Tmax ^ 4 ≤ 0) :
    radiatorRate C Krad Q Tmax ≤ 0 := by
  unfold radiatorRate
  exact div_nonpos_of_nonpos_of_nonneg h (le_of_lt hC)

private lemma slope_tendsto_of_within {f : ℝ → ℝ} {f' x : ℝ} {s t : Set ℝ}
    (h : HasDerivWithinAt f f' s x) (hts : t ⊆ s) (htx : t ⊆ {x}ᶜ) :
    Filter.Tendsto (fun y => (f y - f x) / (y - x)) (nhdsWithin x t) (nhds f') := by
  have hE := hasDerivWithinAt_iff_tendsto.mp h
  have hE' : Filter.Tendsto (fun y => ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f'‖)
      (nhdsWithin x t) (nhds 0) :=
    hE.mono_left (nhdsWithin_mono x hts)
  have hcongr : (fun y => ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f'‖) =ᶠ[nhdsWithin x t]
      (fun y => ‖(f y - f x) / (y - x) - f'‖) := by
    show ∀ᶠ y in nhdsWithin x t,
      ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f'‖ = ‖(f y - f x) / (y - x) - f'‖
    rw [eventually_nhdsWithin_iff]
    filter_upwards with y hyt
    have hyx : y ≠ x := by
      have hmem := htx hyt
      simpa using hmem
    have hyx0 : y - x ≠ 0 := sub_ne_zero.mpr hyx
    have halg : (f y - f x) / (y - x) - f' = (f y - f x - (y - x) * f') / (y - x) := by
      field_simp
    rw [halg, norm_div, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_eq_norm]
  exact Filter.Tendsto.congr' hcongr hE'

private lemma deriv_le_zero_of_isMaxOn {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmax : IsMaxOn f s x) (hmem : s ∈ nhds x) :
    f' ≤ 0 := by
  have hT : Filter.Tendsto (fun y => (f y - f x) / (y - x))
      (nhdsWithin x (Set.Ioi x)) (nhds f') :=
    slope_tendsto_of_within hderiv.hasDerivWithinAt (Set.subset_univ _)
      (fun y hy => by simpa using ne_of_gt hy)
  have hev : ∀ᶠ y in nhdsWithin x (Set.Ioi x), (f y - f x) / (y - x) ≤ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hmem] with y hys hyIoi
    have h1 : f y - f x ≤ 0 :=
      sub_nonpos.mpr (Filter.eventually_principal.mp hmax y hys)
    have h2 : (0 : ℝ) < y - x := sub_pos.mpr hyIoi
    exact div_nonpos_of_nonpos_of_nonneg h1 (le_of_lt h2)
  exact le_of_tendsto hT hev

private lemma deriv_ge_zero_of_isMaxOn {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmax : IsMaxOn f s x) (hmem : s ∈ nhds x) :
    0 ≤ f' := by
  have hT : Filter.Tendsto (fun y => (f y - f x) / (y - x))
      (nhdsWithin x (Set.Iio x)) (nhds f') :=
    slope_tendsto_of_within hderiv.hasDerivWithinAt (Set.subset_univ _)
      (fun y hy => by simpa using ne_of_lt hy)
  have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x), 0 ≤ (f y - f x) / (y - x) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hmem] with y hys hyIio
    have h1 : f y - f x ≤ 0 :=
      sub_nonpos.mpr (Filter.eventually_principal.mp hmax y hys)
    have h2 : y - x < 0 := sub_neg.mpr hyIio
    have h3 : (0 : ℝ) ≤ (-(f y - f x)) / (-(y - x)) :=
      div_nonneg (neg_nonneg.mpr h1) (le_of_lt (neg_pos.mpr h2))
    rwa [neg_div_neg_eq] at h3
  exact ge_of_tendsto hT hev

private lemma deriv_ge_zero_of_isMinOn {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmin : IsMinOn f s x) (hmem : s ∈ nhds x) :
    0 ≤ f' := by
  have hT : Filter.Tendsto (fun y => (f y - f x) / (y - x))
      (nhdsWithin x (Set.Ioi x)) (nhds f') :=
    slope_tendsto_of_within hderiv.hasDerivWithinAt (Set.subset_univ _)
      (fun y hy => by simpa using ne_of_gt hy)
  have hev : ∀ᶠ y in nhdsWithin x (Set.Ioi x), 0 ≤ (f y - f x) / (y - x) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hmem] with y hys hyIoi
    have h1 : 0 ≤ f y - f x :=
      sub_nonneg.mpr (Filter.eventually_principal.mp hmin y hys)
    have h2 : (0 : ℝ) < y - x := sub_pos.mpr hyIoi
    exact div_nonneg h1 (le_of_lt h2)
  exact ge_of_tendsto hT hev

private lemma deriv_le_zero_of_isMinOn {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmin : IsMinOn f s x) (hmem : s ∈ nhds x) :
    f' ≤ 0 := by
  have hT : Filter.Tendsto (fun y => (f y - f x) / (y - x))
      (nhdsWithin x (Set.Iio x)) (nhds f') :=
    slope_tendsto_of_within hderiv.hasDerivWithinAt (Set.subset_univ _)
      (fun y hy => by simpa using ne_of_lt hy)
  have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x), (f y - f x) / (y - x) ≤ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hmem] with y hys hyIio
    have h1 : 0 ≤ f y - f x :=
      sub_nonneg.mpr (Filter.eventually_principal.mp hmin y hys)
    have h2 : y - x < 0 := sub_neg.mpr hyIio
    have h3 : (-(f y - f x)) / (-(y - x)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h1) (le_of_lt (neg_pos.mpr h2))
    rwa [neg_div_neg_eq] at h3
  exact le_of_tendsto hT hev

private lemma fermat_max {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmax : IsMaxOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 :=
  le_antisymm (deriv_le_zero_of_isMaxOn hderiv hmax hmem)
    (deriv_ge_zero_of_isMaxOn hderiv hmax hmem)

private lemma fermat_min {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hderiv : HasDerivAt f f' x) (hmin : IsMinOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 :=
  le_antisymm (deriv_le_zero_of_isMinOn hderiv hmin hmem)
    (deriv_ge_zero_of_isMinOn hderiv hmin hmem)

private lemma rolle {f : ℝ → ℝ} {f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (heq : f a = f b) : ∃ c ∈ Set.Ioo a b, f' c = 0 := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_refl a, le_of_lt hab⟩
  obtain ⟨xmax, hxmaxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, le_of_lt hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_refl b⟩
  by_cases hmax : f xmax = f a
  · have hle : ∀ x ∈ Set.Icc a b, f x ≤ f a := by
      intro x hx
      have h1 := Filter.eventually_principal.mp hxmax x hx
      linarith
    obtain ⟨xmin, hminmem, hhmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
    by_cases hmineq : f xmin = f a
    · have hconst : ∀ x ∈ Set.Icc a b, f x = f a := by
        intro x hx
        apply le_antisymm (hle x hx)
        have h2 := Filter.eventually_principal.mp hhmin x hx
        linarith
      have hcmem : (a + b) / 2 ∈ Set.Ioo a b := by
        constructor <;> linarith
      have hcIcc : (a + b) / 2 ∈ Set.Icc a b :=
        ⟨le_of_lt hcmem.1, le_of_lt hcmem.2⟩
      have hmaxc : IsMaxOn f (Set.Icc a b) ((a + b) / 2) := by
        show ∀ᶠ y in Filter.principal (Set.Icc a b), f y ≤ f ((a + b) / 2)
        rw [Filter.eventually_principal]
        intro x hx
        have e1 := hconst x hx
        have e2 := hconst ((a + b) / 2) hcIcc
        linarith
      have h0 := fermat_max (hderiv ((a + b) / 2) hcmem) hmaxc
        (Icc_mem_nhds hcmem.1 hcmem.2)
      exact ⟨(a + b) / 2, hcmem, h0⟩
    · have hlt : f xmin < f a := by
        have h2 := Filter.eventually_principal.mp hhmin a ha_mem
        exact lt_of_le_of_ne h2 hmineq
      have hxa : xmin ≠ a := by
        intro hcon
        rw [hcon] at hlt
        exact lt_irrefl _ hlt
      have hxb : xmin ≠ b := by
        intro hcon
        rw [hcon, heq] at hlt
        exact lt_irrefl _ hlt
      have hIoo : xmin ∈ Set.Ioo a b := by
        have ⟨h1, h2⟩ := hminmem
        exact ⟨lt_of_le_of_ne h1 (Ne.symm hxa), lt_of_le_of_ne h2 hxb⟩
      have h0 := fermat_min (hderiv xmin hIoo) hhmin (Icc_mem_nhds hIoo.1 hIoo.2)
      exact ⟨xmin, hIoo, h0⟩
  · have hgt : f a < f xmax := by
      have h1 := Filter.eventually_principal.mp hxmax a ha_mem
      exact lt_of_le_of_ne h1 (Ne.symm hmax)
    have hxa : xmax ≠ a := by
      intro hcon
      rw [hcon] at hgt
      exact lt_irrefl _ hgt
    have hxb : xmax ≠ b := by
      intro hcon
      rw [hcon, heq] at hgt
      exact lt_irrefl _ hgt
    have hIoo : xmax ∈ Set.Ioo a b := by
      have ⟨h1, h2⟩ := hxmaxmem
      exact ⟨lt_of_le_of_ne h1 (Ne.symm hxa), lt_of_le_of_ne h2 hxb⟩
    have h0 := fermat_max (hderiv xmax hIoo) hxmax (Icc_mem_nhds hIoo.1 hIoo.2)
    exact ⟨xmax, hIoo, h0⟩

private lemma hasDerivAt_psi {f : ℝ → ℝ} {f' x a c : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => f y - (y - a) * c) (f' - c) x := by
  have h' := hasDerivAt_iff_isLittleO.mp h
  have hfun : (fun y : ℝ => (f y - (y - a) * c) - (f x - (x - a) * c) - (y - x) • (f' - c))
      = (fun y : ℝ => f y - f x - (y - x) • f') := by
    ext y
    simp only [smul_eq_mul]
    ring
  rw [hasDerivAt_iff_isLittleO]
  show (fun y : ℝ => (f y - (y - a) * c) - (f x - (x - a) * c) - (y - x) • (f' - c)) =o[nhds x]
    fun y => y - x
  rw [hfun]
  exact h'

private lemma mvt {f : ℝ → ℝ} {f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f b - f a = (b - a) * f' c := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  set slope : ℝ := (f b - f a) / (b - a) with hslope
  have hslope_eq : (b - a) * slope = f b - f a := by
    rw [hslope]
    field_simp
  have hlin : ContinuousOn (fun y : ℝ => (y - a) * slope) (Set.Icc a b) :=
    (continuousOn_id.sub continuousOn_const).mul_const slope
  have hpsi_cont : ContinuousOn (fun y => f y - (y - a) * slope) (Set.Icc a b) :=
    hcont.sub hlin
  have hpsi_deriv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => f y - (y - a) * slope) (f' x - slope) x :=
    fun x hx => hasDerivAt_psi (hderiv x hx)
  have hpsi_a : (fun y => f y - (y - a) * slope) a = f a := by simp
  have hpsi_b : (fun y => f y - (y - a) * slope) b = f a := by
    show f b - (b - a) * slope = f a
    linarith [hslope_eq]
  have heq : (fun y => f y - (y - a) * slope) a = (fun y => f y - (y - a) * slope) b := by
    rw [hpsi_a, hpsi_b]
  obtain ⟨c, hcIoo, hc0⟩ := rolle hab hpsi_cont
    (fun x hx => hpsi_deriv x hx) heq
  refine ⟨c, hcIoo, ?_⟩
  have hc0' : f' c - slope = 0 := hc0
  have hfc : f' c = slope := by linarith [hc0']
  rw [hfc]
  linarith [hslope_eq]

private lemma ici_mem_nhds {c : ℝ} (hc : 0 < c) : Set.Ici 0 ∈ nhds c :=
  Filter.mem_of_superset (Ioi_mem_nhds hc) Set.Ioi_subset_Ici_self

private lemma exists_last_time_le {f : ℝ → ℝ} {B t : ℝ} (ht : 0 ≤ t)
    (hB0 : f 0 ≤ B) (hcont : ∀ x ∈ Set.Icc 0 t, ContinuousWithinAt f (Set.Ici 0) x) :
    ∃ s0 ∈ Set.Icc 0 t, f s0 ≤ B ∧ (∀ u ∈ Set.Icc 0 t, s0 < u → B < f u) ∧
    (s0 < t → f s0 = B) := by
  set G : Set ℝ := {s | s ∈ Set.Icc 0 t ∧ f s ≤ B} with hG
  have memG : ∀ {s}, s ∈ G ↔ s ∈ Set.Icc 0 t ∧ f s ≤ B := fun {s} => Iff.rfl
  have h0mem : 0 ∈ G := memG.mpr ⟨⟨le_refl 0, ht⟩, hB0⟩
  have hne : G.Nonempty := ⟨0, h0mem⟩
  have hbdd : BddAbove G := ⟨t, fun s hs => ((memG.mp hs).1).2⟩
  set s0 : ℝ := sSup G with hs0
  have hs0lo : 0 ≤ s0 := le_csSup hbdd h0mem
  have hs0hi : s0 ≤ t := csSup_le hne (fun s hs => ((memG.mp hs).1).2)
  have hs0mem : s0 ∈ Set.Icc 0 t := ⟨hs0lo, hs0hi⟩
  have hle : f s0 ≤ B := by
    by_cases hmem : s0 ∈ G
    · exact (memG.mp hmem).2
    · have hs0pos : 0 < s0 := by
        have hne0 : s0 ≠ 0 := by
          intro hcon
          rw [hcon] at hmem
          exact hmem h0mem
        exact lt_of_le_of_ne hs0lo (Ne.symm hne0)
      have hcat : ContinuousAt f s0 :=
        (hcont s0 hs0mem).continuousAt (ici_mem_nhds hs0pos)
      by_contra hcon
      have hcon' : B < f s0 := lt_of_not_ge hcon
      have hev : ∀ᶠ y in nhds s0, B < f y := hcat.eventually (eventually_gt_nhds hcon')
      obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff_ball.mp hev
      have hGb : ∃ b ∈ G, s0 - ε / 2 < b := by
        by_contra hcon2
        have hle2 : ∀ b ∈ G, b ≤ s0 - ε / 2 := by
          intro b hb
          by_contra hlt2
          have hlt2' : s0 - ε / 2 < b := lt_of_not_ge hlt2
          exact hcon2 ⟨b, hb, hlt2'⟩
        have hle3 := csSup_le hne hle2
        linarith
      obtain ⟨b, hbG, hbb⟩ := hGb
      have hb_le : b ≤ s0 := le_csSup hbdd hbG
      have hb_ball : b ∈ Metric.ball s0 ε := by
        rw [Metric.mem_ball, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hb_le)]
        linarith [hbb, hεpos]
      have hBlt := hε b hb_ball
      have hBle := (memG.mp hbG).2
      linarith
  have hgt : ∀ u ∈ Set.Icc 0 t, s0 < u → B < f u := by
    intro u hu hlt
    by_contra hcon
    have hcon' : f u ≤ B := le_of_not_gt hcon
    have huG : u ∈ G := memG.mpr ⟨hu, hcon'⟩
    have hleu := le_csSup hbdd huG
    linarith
  have heq : s0 < t → f s0 = B := by
    intro hlt
    apply le_antisymm hle
    by_contra hcon
    have hcon' : f s0 < B := lt_of_not_ge hcon
    have hev2 : ∀ᶠ y in nhdsWithin s0 (Set.Ici 0), f y < B :=
      (hcont s0 hs0mem).eventually (eventually_lt_nhds hcon')
    rw [eventually_nhdsWithin_iff] at hev2
    obtain ⟨ε, hεpos, hε2⟩ := Metric.eventually_nhds_iff_ball.mp hev2
    set δ : ℝ := min (ε / 2) ((t - s0) / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδle1 : δ ≤ ε / 2 := min_le_left _ _
    have hδle2 : δ ≤ (t - s0) / 2 := min_le_right _ _
    have hvball : s0 + δ ∈ Metric.ball s0 ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hring : (s0 + δ) - s0 = δ := by ring
      rw [hring, abs_of_pos hδpos]
      linarith
    have hvIci : s0 + δ ∈ Set.Ici 0 :=
      le_trans hs0lo (le_add_of_nonneg_right (le_of_lt hδpos))
    have hvIcc : s0 + δ ∈ Set.Icc 0 t := by
      refine ⟨?_, ?_⟩
      · exact le_trans hs0lo (le_add_of_nonneg_right (le_of_lt hδpos))
      · linarith [hδle2, hs0hi]
    have hfvB := hε2 (s0 + δ) hvball hvIci
    have hBfv := hgt (s0 + δ) hvIcc (by linarith : s0 < s0 + δ)
    linarith
  exact ⟨s0, hs0mem, hle, hgt, heq⟩

private lemma exists_last_time_ge {T : ℝ → ℝ} {B t : ℝ} (ht : 0 ≤ t)
    (hB0 : B ≤ T 0) (hcont : ∀ x ∈ Set.Icc 0 t, ContinuousWithinAt T (Set.Ici 0) x) :
    ∃ s0 ∈ Set.Icc 0 t, B ≤ T s0 ∧ (∀ u ∈ Set.Icc 0 t, s0 < u → T u < B) ∧
    (s0 < t → T s0 = B) := by
  have hcont' : ∀ x ∈ Set.Icc 0 t, ContinuousWithinAt (-T) (Set.Ici 0) x :=
    fun x hx => (hcont x hx).neg
  have hB0' : (-T) 0 ≤ -B := by
    show -(T 0) ≤ -B
    exact neg_le_neg hB0
  obtain ⟨s0, hs0mem, hs0le, hs0gt, hs0eq⟩ :=
    exists_last_time_le ht hB0' hcont'
  refine ⟨s0, hs0mem, ?_, ?_, ?_⟩
  · have hs0le' : -(T s0) ≤ -B := hs0le
    exact neg_le_neg_iff.mp hs0le'
  · intro u hu hlt
    have h1 : -B < (-T) u := hs0gt u hu hlt
    have h1' : -B < -(T u) := h1
    exact neg_lt_neg_iff.mp h1'
  · intro hlt
    have h1 : (-T) s0 = -B := hs0eq hlt
    have h1' : -(T s0) = -B := h1
    exact neg_inj.mp h1'

/-- Box trapping for an actual forward solution: if `T` has
within-derivative `radiatorRate C Krad Q (T s)` on `Set.Ici 0` at
every `s ≥ 0`, with `0 ≤ Tmin ≤ Tmax`, the inward signs above, and
`T 0 ∈ [Tmin, Tmax]`, then `T t ∈ [Tmin, Tmax]` for every `t ≥ 0`:
on the box the trajectory solves the original (unclipped) field. -/
theorem radiator_solution_trapped {C Krad Q Tmin Tmax : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax)
    (hlo : 0 ≤ Q - Krad * Tmin ^ 4) (hhi : Q - Krad * Tmax ^ 4 ≤ 0)
    {T : ℝ → ℝ}
    (hT : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt T (radiatorRate C Krad Q (T s)) (Set.Ici 0) s)
    (h0 : T 0 ∈ Set.Icc Tmin Tmax) {t : ℝ} (ht : 0 ≤ t) :
    T t ∈ Set.Icc Tmin Tmax := by
  have h0le : Tmin ≤ T 0 ∧ T 0 ≤ Tmax := h0
  have hTmax0 : (0 : ℝ) ≤ Tmax := le_trans hmin hmax
  have hcont : ∀ x ∈ Set.Icc 0 t, ContinuousWithinAt T (Set.Ici 0) x := by
    intro x hx
    exact (hT x hx.1).continuousWithinAt
  have hcontOn : ∀ a b : ℝ, 0 ≤ a → ContinuousOn T (Set.Icc a b) := by
    intro a b ha x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hcw : Filter.Tendsto T (nhdsWithin x (Set.Ici 0)) (nhds (T x)) :=
      (hT x hx0).continuousWithinAt
    have hsub : Set.Icc a b ⊆ Set.Ici 0 := fun y hy => le_trans ha hy.1
    exact hcw.mono_left (nhdsWithin_mono x hsub)
  have hderivAt : ∀ x : ℝ, 0 < x → HasDerivAt T (radiatorRate C Krad Q (T x)) x := by
    intro x hx
    exact (hT x (le_of_lt hx)).hasDerivAt (ici_mem_nhds hx)
  have hupper : T t ≤ Tmax := by
    by_contra hcon
    have htt : Tmax < T t := lt_of_not_ge hcon
    obtain ⟨s0, hs0mem, hs0le, hs0gt, hs0eq⟩ :=
      exists_last_time_le ht h0le.2 hcont
    have hs0lt : s0 < t := by
      have hne : s0 ≠ t := by
        intro hcon2
        rw [hcon2] at hs0le
        linarith [htt]
      exact lt_of_le_of_ne hs0mem.2 hne
    have hs0eq' : T s0 = Tmax := hs0eq hs0lt
    obtain ⟨c, hcIoo, hcEq0⟩ := mvt hs0lt (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hcEq : T t - T s0 = (t - s0) * radiatorRate C Krad Q (T c) := hcEq0
    have hcIcc : c ∈ Set.Icc 0 t :=
      ⟨le_trans hs0mem.1 (le_of_lt hcIoo.1), le_of_lt hcIoo.2⟩
    have hTc : Tmax < T c := hs0gt c hcIcc hcIoo.1
    have hrate : radiatorRate C Krad Q (T c) < 0 := by
      unfold radiatorRate
      have hpow : Tmax ^ 4 < (T c) ^ 4 :=
        pow_lt_pow_left₀ hTc hTmax0 (by decide : (4 : ℕ) ≠ 0)
      have hKpow : Krad * Tmax ^ 4 < Krad * (T c) ^ 4 :=
        mul_lt_mul_of_pos_left hpow hK
      have hnum : Q - Krad * (T c) ^ 4 < 0 := by linarith [hhi, hKpow]
      exact div_neg_of_neg_of_pos hnum hC
    have hneg : (t - s0) * radiatorRate C Krad Q (T c) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hs0lt) hrate
    rw [hs0eq'] at hcEq
    linarith [hcEq, htt, hneg]
  have hlower : Tmin ≤ T t := by
    by_cases hQ : Q = 0
    · have hTmin0 : Tmin = 0 := by
        by_contra hconT
        have hTpos : 0 < Tmin := lt_of_le_of_ne hmin (Ne.symm hconT)
        have h4pos : 0 < Tmin ^ 4 := pow_pos hTpos 4
        have hK4pos : 0 < Krad * Tmin ^ 4 := mul_pos hK h4pos
        linarith [hlo, hQ]
      rw [hTmin0]
      by_contra hconTt
      have htt : T t < 0 := lt_of_not_ge hconTt
      obtain ⟨s1, hs1mem, hs1le, hs1gt, hs1eq⟩ :=
        exists_last_time_ge ht (le_trans hmin h0le.1) hcont
      have hs1lt : s1 < t := by
        have hne : s1 ≠ t := by
          intro hcon2
          rw [hcon2] at hs1le
          linarith [htt]
        exact lt_of_le_of_ne hs1mem.2 hne
      have hs1eq' : T s1 = 0 := hs1eq hs1lt
      have hKne : Krad ≠ 0 := ne_of_gt hK
      have perV : ∀ v ∈ Set.Icc 0 t, s1 < v →
          C / ((v - s1) * Krad) ≤ (-T v) ^ 3 := by
        intro v hvIcc hvs1
        have hTvneg : T v < 0 := hs1gt v hvIcc hvs1
        have hwpos : 0 < -T v := neg_pos.mpr hTvneg
        obtain ⟨c, hcIoo, hcEq0⟩ := mvt hvs1 (hcontOn s1 v hs1mem.1)
          (fun x hx => hderivAt x (lt_of_le_of_lt hs1mem.1 hx.1))
        have hcEq : T v - T s1 = (v - s1) * radiatorRate C Krad Q (T c) := hcEq0
        rw [hs1eq'] at hcEq
        have hratec : radiatorRate C Krad Q (T c) = -(Krad * (T c) ^ 4 / C) := by
          unfold radiatorRate
          rw [hQ]
          ring
        rw [hratec] at hcEq
        have hcv : c < v := hcIoo.2
        have hc0 : 0 ≤ c := le_trans hs1mem.1 (le_of_lt hcIoo.1)
        have hcIcc : c ∈ Set.Icc 0 t :=
          ⟨hc0, le_of_lt (lt_of_lt_of_le hcIoo.2 hvIcc.2)⟩
        have hcneg : T c < 0 := hs1gt c hcIcc hcIoo.1
        have hTcle : T v ≤ T c := by
          obtain ⟨d, hdIoo, hdEq0⟩ := mvt hcv (hcontOn c v hc0)
            (fun x hx => hderivAt x (lt_of_le_of_lt hc0 hx.1))
          have hdEq : T v - T c = (v - c) * radiatorRate C Krad Q (T d) := hdEq0
          have hrated : radiatorRate C Krad Q (T d) ≤ 0 := by
            unfold radiatorRate
            rw [hQ]
            have hsq : (0 : ℝ) ≤ (T d) ^ 2 := sq_nonneg _
            have h4eq : (T d) ^ 4 = ((T d) ^ 2) ^ 2 := by ring
            have h4nn : (0 : ℝ) ≤ (T d) ^ 4 := by
              rw [h4eq]
              exact pow_nonneg hsq 2
            have hnum : 0 - Krad * (T d) ^ 4 ≤ 0 := by
              have hnn := mul_nonneg (le_of_lt hK) h4nn
              linarith
            exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hC)
          have hprod : (v - c) * radiatorRate C Krad Q (T d) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt (sub_pos.mpr hcv)) hrated
          linarith [hdEq]
        have habs : |T c| ≤ |T v| := by
          rw [abs_of_neg hcneg, abs_of_neg hTvneg]
          exact neg_le_neg hTcle
        have h4le : (T c) ^ 4 ≤ (-T v) ^ 4 := by
          have h1 : |T c| ^ 4 ≤ |T v| ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
          rw [Even.pow_abs ⟨2, rfl⟩, Even.pow_abs ⟨2, rfl⟩] at h1
          have hneg4 : (-T v) ^ 4 = (T v) ^ 4 := by ring
          rw [hneg4]
          exact h1
        have hwEq : -T v = (v - s1) * (Krad * (T c) ^ 4 / C) := by linarith [hcEq]
        have hble : (v - s1) * (Krad * (T c) ^ 4 / C) ≤ (v - s1) * (Krad * (-T v) ^ 4 / C) := by
          have hKK : Krad * (T c) ^ 4 / C ≤ Krad * (-T v) ^ 4 / C := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h4le (le_of_lt hK)) (le_of_lt (inv_pos.mpr hC))
          exact mul_le_mul_of_nonneg_left hKK (le_of_lt (sub_pos.mpr hvs1))
        have hvsK : 0 < (v - s1) * Krad := mul_pos (sub_pos.mpr hvs1) hK
        rw [div_le_iff₀ hvsK]
        have h1 : -T v ≤ (v - s1) * (Krad * (-T v) ^ 4 / C) := by linarith [hwEq, hble]
        have hrw : (v - s1) * (Krad * (-T v) ^ 4 / C) = ((v - s1) * Krad * (-T v) ^ 4) / C := by ring
        rw [hrw] at h1
        have h2 : (-T v) * C ≤ (v - s1) * Krad * (-T v) ^ 4 := (le_div_iff₀ hC).mp h1
        have hw43 : (-T v) ^ 4 = (-T v) ^ 3 * (-T v) := by ring
        rw [hw43] at h2
        exact le_of_mul_le_mul_right (by linarith [h2]) hwpos
      have hevT : ∀ᶠ y in nhdsWithin s1 (Set.Ici 0), -1 < T y := by
        have hneg1 : (-1 : ℝ) < T s1 := by linarith [hs1eq']
        have h1 : ∀ᶠ y in nhds (T s1), -1 < y := eventually_gt_nhds hneg1
        exact (hcont s1 hs1mem).eventually h1
      rw [eventually_nhdsWithin_iff] at hevT
      obtain ⟨ε, hεpos, hεT⟩ := Metric.eventually_nhds_iff_ball.mp hevT
      have hCK : 0 < C / Krad := div_pos hC hK
      set δ : ℝ := min (ε / 2) (min ((t - s1) / 2) (C / Krad / 2)) with hδ
      have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith [hs1lt]) (by linarith))
      have hδle1 : δ ≤ ε / 2 := min_le_left _ _
      have hδle2 : δ ≤ (t - s1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδle3 : δ ≤ C / Krad / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      set v : ℝ := s1 + δ with hv
      have hvs1 : s1 < v := by linarith [hδpos]
      have hvball : v ∈ Metric.ball s1 ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hring : v - s1 = δ := by rw [hv]; ring
        rw [hring, abs_of_pos hδpos]
        linarith [hδle1, hεpos]
      have hvIci : v ∈ Set.Ici 0 :=
        le_trans hs1mem.1 (le_add_of_nonneg_right (le_of_lt hδpos))
      have hvIcc : v ∈ Set.Icc 0 t := by
        refine ⟨?_, ?_⟩
        · exact le_trans hs1mem.1 (le_add_of_nonneg_right (le_of_lt hδpos))
        · have hvle : v ≤ s1 + (t - s1) / 2 := by rw [hv]; linarith [hδle2]
          linarith [hvle, hs1mem.2]
      have hw1 : -T v < 1 := by
        have hTv : -1 < T v := hεT v hvball hvIci
        linarith
      have hbound := perV v hvIcc hvs1
      have hsmall : (v - s1) * Krad < C := by
        have hvs1eq : v - s1 = δ := by rw [hv]; ring
        rw [hvs1eq]
        have h1 : δ * Krad ≤ (C / Krad / 2) * Krad :=
          mul_le_mul_of_nonneg_right hδle3 (le_of_lt hK)
        have h2 : (C / Krad / 2) * Krad = C / 2 := by field_simp
        linarith [h1, h2, hC]
      have hCdiv : (1 : ℝ) < C / ((v - s1) * Krad) := by
        rw [lt_div_iff₀ (mul_pos (sub_pos.mpr hvs1) hK)]
        linarith [hsmall]
      have hw13 : (1 : ℝ) ^ 3 < (-T v) ^ 3 := by
        have h := lt_of_lt_of_le hCdiv hbound
        simpa using h
      have hww : (0 : ℝ) ≤ -T v := le_of_lt (neg_pos.mpr (hs1gt v hvIcc hvs1))
      have hwgt1 : (1 : ℝ) < -T v :=
        (pow_lt_pow_iff_left₀ zero_le_one hww (by decide : (3 : ℕ) ≠ 0)).mp hw13
      linarith [hw1]
    · have hQnn : 0 ≤ Q := by
        have h4nn : 0 ≤ Krad * Tmin ^ 4 := mul_nonneg (le_of_lt hK) (pow_nonneg hmin 4)
        linarith [hlo]
      have hQpos : 0 < Q := lt_of_le_of_ne hQnn (Ne.symm hQ)
      have hnonneg : ∀ u ∈ Set.Icc 0 t, 0 ≤ T u := by
        intro u hu
        by_contra hcon
        have huu : T u < 0 := lt_of_not_ge hcon
        obtain ⟨s1, hs1mem, hs1le, hs1gt, hs1eq⟩ :=
          exists_last_time_ge hu.1 (le_trans hmin h0le.1)
            (fun x hx => hcont x ⟨hx.1, le_trans hx.2 hu.2⟩)
        have hs1lt : s1 < u := by
          have hne : s1 ≠ u := by
            intro hcon2
            rw [hcon2] at hs1le
            linarith [huu]
          exact lt_of_le_of_ne hs1mem.2 hne
        have hs1eq' : T s1 = 0 := hs1eq hs1lt
        have hrate0 : radiatorRate C Krad Q (T s1) = Q / C := by
          unfold radiatorRate
          rw [hs1eq']
          have h04 : (0 : ℝ) ^ 4 = 0 := zero_pow (by decide : (4 : ℕ) ≠ 0)
          rw [h04]
          ring
        have hratepos : 0 < radiatorRate C Krad Q (T s1) := by
          rw [hrate0]
          exact div_pos hQpos hC
        have hslope : Filter.Tendsto (fun y => (T y - T s1) / (y - s1))
            (nhdsWithin s1 (Set.Ioi s1)) (nhds (radiatorRate C Krad Q (T s1))) :=
          slope_tendsto_of_within (hT s1 hs1mem.1)
            (fun y hy => le_of_lt (lt_of_le_of_lt hs1mem.1 hy))
            (fun y hy => by simpa using ne_of_gt hy)
        have hev : ∀ᶠ y in nhdsWithin s1 (Set.Ioi s1), (T y - T s1) / (y - s1) < 0 := by
          rw [eventually_nhdsWithin_iff]
          filter_upwards [Iio_mem_nhds hs1lt] with y hyIio hyIoi
          have hyIcc : y ∈ Set.Icc 0 u :=
            ⟨le_of_lt (lt_of_le_of_lt hs1mem.1 hyIoi), le_of_lt hyIio⟩
          have hTy : T y < 0 := hs1gt y hyIcc hyIoi
          have hnum : T y - T s1 < 0 := by rw [hs1eq']; linarith [hTy]
          have hden : (0 : ℝ) < y - s1 := sub_pos.mpr hyIoi
          exact div_neg_of_neg_of_pos hnum hden
        have hle0 := le_of_tendsto hslope (hev.mono fun y hy => le_of_lt hy)
        linarith [hratepos, hle0]
      by_contra hconL
      have htt : T t < Tmin := lt_of_not_ge hconL
      obtain ⟨s0, hs0mem, hs0le, hs0gt, hs0eq⟩ :=
        exists_last_time_ge ht h0le.1 hcont
      have hs0lt : s0 < t := by
        have hne : s0 ≠ t := by
          intro hcon2
          rw [hcon2] at hs0le
          linarith [htt]
        exact lt_of_le_of_ne hs0mem.2 hne
      have hs0eq' : T s0 = Tmin := hs0eq hs0lt
      obtain ⟨c, hcIoo, hcEq0⟩ := mvt hs0lt (hcontOn s0 t hs0mem.1)
        (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
      have hcEq : T t - T s0 = (t - s0) * radiatorRate C Krad Q (T c) := hcEq0
      have hcIcc : c ∈ Set.Icc 0 t :=
        ⟨le_trans hs0mem.1 (le_of_lt hcIoo.1), le_of_lt hcIoo.2⟩
      have hTc : T c < Tmin := hs0gt c hcIcc hcIoo.1
      have hTc0 : 0 ≤ T c := hnonneg c hcIcc
      have hrate : 0 < radiatorRate C Krad Q (T c) := by
        unfold radiatorRate
        have hpow : (T c) ^ 4 < Tmin ^ 4 :=
          pow_lt_pow_left₀ hTc hTc0 (by decide : (4 : ℕ) ≠ 0)
        have hKpow : Krad * (T c) ^ 4 < Krad * Tmin ^ 4 :=
          mul_lt_mul_of_pos_left hpow hK
        have hnum : 0 < Q - Krad * (T c) ^ 4 := by linarith [hlo, hKpow]
        exact div_pos hnum hC
      have hpos : 0 < (t - s0) * radiatorRate C Krad Q (T c) :=
        mul_pos (sub_pos.mpr hs0lt) hrate
      rw [hs0eq'] at hcEq
      linarith [hcEq, htt, hpos]
  exact ⟨hlower, hupper⟩

/-- Box trapping for a solution of the CLIPPED field: if `T` has
within-derivative `clippedRadiatorRate C Krad Q Tmin Tmax (T s)` on
`Set.Ici 0` at every `s ≥ 0`, with the same inward signs, and
`T 0 ∈ [Tmin, Tmax]`, then `T t ∈ [Tmin, Tmax]` for every `t ≥ 0`.
On the box the clipped and physical rates agree, so such a
trajectory also solves the original field there. -/
theorem clippedRadiator_solution_trapped {C Krad Q Tmin Tmax : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax)
    (hlo : 0 ≤ Q - Krad * Tmin ^ 4) (hhi : Q - Krad * Tmax ^ 4 ≤ 0)
    {T : ℝ → ℝ}
    (hT : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T s)) (Set.Ici 0) s)
    (h0 : T 0 ∈ Set.Icc Tmin Tmax) {t : ℝ} (ht : 0 ≤ t) :
    T t ∈ Set.Icc Tmin Tmax := by
  have _ := hK
  have _ := hmin
  have h0le : Tmin ≤ T 0 ∧ T 0 ≤ Tmax := h0
  have hcont : ∀ x ∈ Set.Icc 0 t, ContinuousWithinAt T (Set.Ici 0) x := by
    intro x hx
    exact (hT x hx.1).continuousWithinAt
  have hcontOn : ∀ a b : ℝ, 0 ≤ a → ContinuousOn T (Set.Icc a b) := by
    intro a b ha x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hcw : Filter.Tendsto T (nhdsWithin x (Set.Ici 0)) (nhds (T x)) :=
      (hT x hx0).continuousWithinAt
    have hsub : Set.Icc a b ⊆ Set.Ici 0 := fun y hy => le_trans ha hy.1
    exact hcw.mono_left (nhdsWithin_mono x hsub)
  have hderivAt : ∀ x : ℝ, 0 < x →
      HasDerivAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T x)) x := by
    intro x hx
    exact (hT x (le_of_lt hx)).hasDerivAt (ici_mem_nhds hx)
  have hupper : T t ≤ Tmax := by
    by_contra hcon
    have htt : Tmax < T t := lt_of_not_ge hcon
    obtain ⟨s0, hs0mem, hs0le, hs0gt, hs0eq⟩ :=
      exists_last_time_le ht h0le.2 hcont
    have hs0lt : s0 < t := by
      have hne : s0 ≠ t := by
        intro hcon2
        rw [hcon2] at hs0le
        linarith [htt]
      exact lt_of_le_of_ne hs0mem.2 hne
    have hs0eq' : T s0 = Tmax := hs0eq hs0lt
    obtain ⟨c, hcIoo, hcEq0⟩ := mvt hs0lt (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hcEq : T t - T s0 = (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) := hcEq0
    have hcIcc : c ∈ Set.Icc 0 t :=
      ⟨le_trans hs0mem.1 (le_of_lt hcIoo.1), le_of_lt hcIoo.2⟩
    have hTc : Tmax < T c := hs0gt c hcIcc hcIoo.1
    have hclip : min (max (T c) Tmin) Tmax = Tmax := by
      rw [max_eq_left (le_trans hmax (le_of_lt hTc)), min_eq_right (le_of_lt hTc)]
    have hrate : clippedRadiatorRate C Krad Q Tmin Tmax (T c) ≤ 0 := by
      unfold clippedRadiatorRate
      rw [hclip]
      exact radiatorRate_nonpos_at_max hC hhi
    have hnonpos : (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (sub_pos.mpr hs0lt)) hrate
    rw [hs0eq'] at hcEq
    linarith [hcEq, htt, hnonpos]
  have hlower : Tmin ≤ T t := by
    by_contra hcon
    have htt : T t < Tmin := lt_of_not_ge hcon
    obtain ⟨s0, hs0mem, hs0le, hs0gt, hs0eq⟩ :=
      exists_last_time_ge ht h0le.1 hcont
    have hs0lt : s0 < t := by
      have hne : s0 ≠ t := by
        intro hcon2
        rw [hcon2] at hs0le
        linarith [htt]
      exact lt_of_le_of_ne hs0mem.2 hne
    have hs0eq' : T s0 = Tmin := hs0eq hs0lt
    obtain ⟨c, hcIoo, hcEq0⟩ := mvt hs0lt (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hcEq : T t - T s0 = (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) := hcEq0
    have hcIcc : c ∈ Set.Icc 0 t :=
      ⟨le_trans hs0mem.1 (le_of_lt hcIoo.1), le_of_lt hcIoo.2⟩
    have hTc : T c < Tmin := hs0gt c hcIcc hcIoo.1
    have hclip : min (max (T c) Tmin) Tmax = Tmin := by
      rw [max_eq_right (le_of_lt hTc), min_eq_left hmax]
    have hrate : 0 ≤ clippedRadiatorRate C Krad Q Tmin Tmax (T c) := by
      unfold clippedRadiatorRate
      rw [hclip]
      exact radiatorRate_nonneg_at_min hC hlo
    have hnonneg : 0 ≤ (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) :=
      mul_nonneg (le_of_lt (sub_pos.mpr hs0lt)) hrate
    rw [hs0eq'] at hcEq
    linarith [hcEq, htt, hnonneg]
  exact ⟨hlower, hupper⟩

/-- On the box, a clipped-field solution has the physical rate as
its within-derivative: the trapped trajectory solves the original
field. -/
lemma clippedRadiator_hasDerivWithinAt {C Krad Q Tmin Tmax : ℝ}
    {T : ℝ → ℝ} {s : ℝ}
    (hT : HasDerivWithinAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T s)) (Set.Ici 0) s)
    (hmem : T s ∈ Set.Icc Tmin Tmax) :
    HasDerivWithinAt T (radiatorRate C Krad Q (T s)) (Set.Ici 0) s := by
  rw [clippedRadiatorRate_eq_of_mem hmem] at hT
  exact hT

private lemma ode_global_exists_of_global_lipschitz
    (v : ℝ → ℝ) (K : NNReal) (hlip : LipschitzWith K v) (x0 : ℝ) :
    ∃ T : ℝ → ℝ, T 0 = x0 ∧ ∀ t : ℝ, HasDerivAt T (v (T t)) t := by
  obtain ⟨T, hT, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun _ x => v x) 0 x0 K
      (hlip.continuous.comp continuous_snd) (fun _ => hlip)
  exact ⟨T, hT.1, hT.2⟩

/-- Existence of the trapped physical solution: for every
`T0 ∈ [Tmin, Tmax]` there is a global trajectory `T` with
`T 0 = T0`, solving the clipped field everywhere
(`HasDerivAt T (clippedRadiatorRate ... (T t)) t` for all `t`),
staying in the box for all `t ≥ 0`, and there solving the
original field (`HasDerivAt T (radiatorRate ... (T t)) t`).
Existence uses the global existence theorem for globally
Lipschitz fields (`ode_global_exists_of_global_lipschitz`) with
the Lipschitz constant from `clippedRadiatorRate_lipschitz`. -/
theorem radiator_solution_exists_trapped {C Krad Q Tmin Tmax T0 : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax)
    (hlo : 0 ≤ Q - Krad * Tmin ^ 4) (hhi : Q - Krad * Tmax ^ 4 ≤ 0)
    (h0 : T0 ∈ Set.Icc Tmin Tmax) :
    ∃ T : ℝ → ℝ, T 0 = T0 ∧
      (∀ t : ℝ, HasDerivAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → T t ∈ Set.Icc Tmin Tmax ∧
        HasDerivAt T (radiatorRate C Krad Q (T t)) t) := by
  have hKnn : 0 ≤ Krad * (4 * Tmax ^ 3) / C := by
    have hT0 : (0 : ℝ) ≤ Tmax := le_trans hmin hmax
    have h3 : (0 : ℝ) ≤ Tmax ^ 3 := pow_nonneg hT0 3
    have h4 : (0 : ℝ) ≤ 4 * Tmax ^ 3 := by linarith
    exact div_nonneg (mul_nonneg (le_of_lt hK) h4) (le_of_lt hC)
  have hlip : LipschitzWith ⟨Krad * (4 * Tmax ^ 3) / C, hKnn⟩
      (clippedRadiatorRate C Krad Q Tmin Tmax) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq, Real.dist_eq]
    exact clippedRadiatorRate_lipschitz hC hK hmin hmax a b
  obtain ⟨T, hT0, hT⟩ :=
    ode_global_exists_of_global_lipschitz _ _ hlip T0
  refine ⟨T, hT0, hT, fun t ht => ?_⟩
  have hTwithin : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T s)) (Set.Ici 0) s :=
    fun s _ => (hT s).hasDerivWithinAt
  have h0T : T 0 ∈ Set.Icc Tmin Tmax := by
    rw [hT0]
    exact h0
  have hmem : T t ∈ Set.Icc Tmin Tmax :=
    clippedRadiator_solution_trapped hC hK hmin hmax hlo hhi hTwithin h0T ht
  have hderiv : HasDerivAt T (radiatorRate C Krad Q (T t)) t := by
    have h := hT t
    rw [clippedRadiatorRate_eq_of_mem hmem] at h
    exact h
  exact ⟨hmem, hderiv⟩

end ThermalPowerPorts
