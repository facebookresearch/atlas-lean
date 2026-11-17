/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.IntermediateValue

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Combustion acoustics and thermal runaway bounds

## i. Overview

Zeroth-order Arrhenius heat generation with Newton cooling,
`C * T' = G * exp(-B / T) - H * (T - Ta)`: an equilibrium exists in
`(Ta, Ta + G / H)` (multiple equilibria are possible; none is
claimed unique), and every forward solution that exists on a
time interval is trapped between `min (T 0) Ta` and
`max (T 0) (Ta + G / H)` on that interval. This is a conditional
trapping statement for solutions that exist; it does not prove
global existence and does not by itself rule out finite-time
blow-up of a maximal solution. Constant reactant and cooling
coefficients are model inputs; no empirical adequacy is claimed.

## ii. Key results

- `Chemistry.CombustionAcoustics.arrhenius_equilibrium_exists`: an equilibrium
  temperature exists in the stated bracket.
- `Chemistry.CombustionAcoustics.arrhenius_solution_trapped`: forward
  solutions are trapped in the stated interval.

## iii. Table of contents

- A. Arrhenius equilibrium and trapping

## iv. References

- The sign bracket is the classical Semenov/Frank-Kamenetskii
  zeroth-order balance; the formal statement is self-contained.

## A. Arrhenius equilibrium and trapping

-/

@[expose] public section

namespace Chemistry.CombustionAcoustics

/-- Zeroth-order Arrhenius heat-release rate with Newton cooling:
`rate(T) = G * exp(-B / T) - H * (T - Ta)`, for heat-generation scale
`G`, cooling coefficient `H`, activation ratio `B = E / R`, and
ambient `Ta`. Read for `T > 0`. -/
noncomputable def arrheniusRate (G H B Ta T : ℝ) : ℝ :=
  G * Real.exp (-B / T) - H * (T - Ta)

/-- At ambient temperature the rate is the positive generation term:
`rate(Ta) = G * exp(-B / Ta)`. -/
lemma arrheniusRate_ambient (G H B Ta : ℝ) :
    arrheniusRate G H B Ta Ta = G * Real.exp (-B / Ta) := by
  unfold arrheniusRate
  ring

/-- The rate is positive at ambient for `G > 0`. -/
lemma arrheniusRate_pos_ambient {G H B Ta : ℝ} (hG : 0 < G) :
    0 < arrheniusRate G H B Ta Ta := by
  rw [arrheniusRate_ambient]
  exact mul_pos hG (Real.exp_pos _)

/-- The rate is positive on `0 < T ≤ Ta` for `G, H > 0`: generation
is positive and cooling is nonpositive there. -/
lemma arrheniusRate_pos_of_le_ambient {G H B Ta T : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hT : 0 < T) (hle : T ≤ Ta) :
    0 < arrheniusRate G H B Ta T := by
  have _hTpos := hT
  have hgen : 0 < G * Real.exp (-B / T) := mul_pos hG (Real.exp_pos _)
  have hcool : H * (T - Ta) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hH) (sub_nonpos.mpr hle)
  have hlt : H * (T - Ta) < G * Real.exp (-B / T) := lt_of_le_of_lt hcool hgen
  unfold arrheniusRate
  exact sub_pos.mpr hlt

/-- At the upper bracket point `Ta + G / H` the rate is negative for
`G, H, B > 0` (with `Ta > 0`): generation is below `G` since
`exp(-B / T) < 1`, and cooling equals `G`. -/
lemma arrheniusRate_neg_at_upper {G H B Ta : ℝ} (hG : 0 < G) (hH : 0 < H)
    (hB : 0 < B) (hTa : 0 < Ta) :
    arrheniusRate G H B Ta (Ta + G / H) < 0 := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hGH : 0 < G / H := div_pos hG hH
  have hTpos : 0 < Ta + G / H := by linarith
  have hexp : Real.exp (-B / (Ta + G / H)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hTpos
  have hgen : G * Real.exp (-B / (Ta + G / H)) < G := by
    calc G * Real.exp (-B / (Ta + G / H)) < G * 1 :=
            mul_lt_mul_of_pos_left hexp hG
      _ = G := mul_one G
  have hcool : H * ((Ta + G / H) - Ta) = G := by
    have h1 : (Ta + G / H) - Ta = G / H := by ring
    rw [h1]
    exact mul_div_cancel₀ G hHne
  have hlt : G * Real.exp (-B / (Ta + G / H)) < H * ((Ta + G / H) - Ta) := by
    rw [hcool]
    exact hgen
  unfold arrheniusRate
  exact sub_neg.mpr hlt

/-- The rate is negative above `Ta + G / H` for `G, H, B > 0`
(with `Ta > 0`): generation is below `G` and cooling exceeds `G`. -/
private lemma arrheniusRate_neg_of_gt_upper {G H B Ta T : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) (hlt : Ta + G / H < T) :
    arrheniusRate G H B Ta T < 0 := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hGH : 0 < G / H := div_pos hG hH
  have hTpos : 0 < T := by linarith
  have hexp : Real.exp (-B / T) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hTpos
  have hgen : G * Real.exp (-B / T) < G := by
    calc G * Real.exp (-B / T) < G * 1 := mul_lt_mul_of_pos_left hexp hG
      _ = G := mul_one G
  have hcool : G < H * (T - Ta) := by
    have h1 : G / H < T - Ta := by linarith
    have h2 : H * (G / H) < H * (T - Ta) := mul_lt_mul_of_pos_left h1 hH
    have h3 : H * (G / H) = G := mul_div_cancel₀ G hHne
    rwa [h3] at h2
  have hlt' : G * Real.exp (-B / T) < H * (T - Ta) := lt_trans hgen hcool
  unfold arrheniusRate
  exact sub_neg.mpr hlt'

/-- The rate is positive at or below `Ta` for `G, H > 0` (with
`Ta > 0`), including nonpositive `T`. -/
private lemma arrheniusRate_pos_of_le_Ta {G H B Ta T : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hTa : 0 < Ta) (hle : T ≤ Ta) :
    0 < arrheniusRate G H B Ta T := by
  rcases lt_or_ge 0 T with hT | hT
  · exact arrheniusRate_pos_of_le_ambient hG hH hT hle
  · have hgen : 0 < G * Real.exp (-B / T) := mul_pos hG (Real.exp_pos _)
    have hcool : H * (T - Ta) < 0 :=
      mul_neg_of_pos_of_neg hH (by linarith)
    have hlt : H * (T - Ta) < G * Real.exp (-B / T) :=
      lt_trans hcool hgen
    unfold arrheniusRate
    exact sub_pos.mpr hlt

/-- A negative within-derivative on `Set.Icc 0 t` at `c > 0`
forces strictly larger values immediately to the left of `c`. -/
private lemma exists_left_gt_of_hasDerivWithinAt_neg_on_interval {T : ℝ → ℝ} {f' c t : ℝ}
    (hT : HasDerivWithinAt T f' (Set.Icc 0 t) c) (hf' : f' < 0) (hc : 0 < c)
    (hct : c ≤ t) :
    ∃ s ∈ Set.Icc (0 : ℝ) t, s < c ∧ T c < T s := by
  rw [hasDerivWithinAt_iff_tendsto] at hT
  have habs : |f'| = -f' := abs_of_neg hf'
  have hK : (0 : ℝ) < |f'| / 2 := by
    rw [habs]
    linarith
  have hev := hT.eventually (eventually_lt_nhds hK)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hu_pos : (0 : ℝ) < min (c / 2) (ε / 2) := lt_min hc2 hε2
  have huc : min (c / 2) (ε / 2) ≤ c / 2 := min_le_left _ _
  have hue : min (c / 2) (ε / 2) < ε :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set u := min (c / 2) (ε / 2) with hu
  have hs0 : (0 : ℝ) ≤ c - u := by linarith
  have hst : c - u ≤ t := by linarith
  have hsc : c - u < c := by linarith
  refine ⟨c - u, Set.mem_Icc.mpr ⟨hs0, hst⟩, hsc, ?_⟩
  have hdist : dist (c - u) c < ε := by
    have hdu : dist (c - u) c = u := by
      rw [dist_eq_norm, show (c - u) - c = -u by ring, norm_neg,
        Real.norm_eq_abs, abs_of_pos hu_pos]
    rw [hdu]
    exact hue
  have hF := hball hdist (Set.mem_Icc.mpr ⟨hs0, hst⟩)
  have hsub : (c - u) - c = -u := by ring
  have hnorm : ‖(c - u) - c‖ = u := by
    rw [hsub, norm_neg, Real.norm_eq_abs, abs_of_pos hu_pos]
  rw [hnorm, hsub, smul_eq_mul] at hF
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hX : ‖T (c - u) - T c - -u * f'‖ < u * (|f'| / 2) := by
    have h := mul_lt_mul_of_pos_left hF hu_pos
    rwa [← mul_assoc, mul_inv_cancel₀ hu_ne, one_mul] at h
  have hfus : -u * f' = u * |f'| := by rw [habs]; ring
  have hrhs : u * (|f'| / 2) = u * |f'| / 2 := by ring
  rw [hfus, hrhs] at hX
  have hle : -‖T (c - u) - T c - u * |f'|‖ ≤ T (c - u) - T c - u * |f'| := by
    rw [Real.norm_eq_abs]
    exact neg_abs_le _
  have hw : (0 : ℝ) < u * |f'| := mul_pos hu_pos (by rw [habs]; linarith)
  linarith

/-- A positive within-derivative on `Set.Icc 0 t` at `c > 0`
forces strictly smaller values immediately to the left of `c`. -/
private lemma exists_left_lt_of_hasDerivWithinAt_pos_on_interval {T : ℝ → ℝ} {f' c t : ℝ}
    (hT : HasDerivWithinAt T f' (Set.Icc 0 t) c) (hf' : 0 < f') (hc : 0 < c)
    (hct : c ≤ t) :
    ∃ s ∈ Set.Icc (0 : ℝ) t, s < c ∧ T s < T c := by
  rw [hasDerivWithinAt_iff_tendsto] at hT
  have habs : |f'| = f' := abs_of_pos hf'
  have hK : (0 : ℝ) < |f'| / 2 := by
    rw [habs]
    linarith
  have hev := hT.eventually (eventually_lt_nhds hK)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hu_pos : (0 : ℝ) < min (c / 2) (ε / 2) := lt_min hc2 hε2
  have huc : min (c / 2) (ε / 2) ≤ c / 2 := min_le_left _ _
  have hue : min (c / 2) (ε / 2) < ε :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set u := min (c / 2) (ε / 2) with hu
  have hs0 : (0 : ℝ) ≤ c - u := by linarith
  have hst : c - u ≤ t := by linarith
  have hsc : c - u < c := by linarith
  refine ⟨c - u, Set.mem_Icc.mpr ⟨hs0, hst⟩, hsc, ?_⟩
  have hdist : dist (c - u) c < ε := by
    have hdu : dist (c - u) c = u := by
      rw [dist_eq_norm, show (c - u) - c = -u by ring, norm_neg,
        Real.norm_eq_abs, abs_of_pos hu_pos]
    rw [hdu]
    exact hue
  have hF := hball hdist (Set.mem_Icc.mpr ⟨hs0, hst⟩)
  have hsub : (c - u) - c = -u := by ring
  have hnorm : ‖(c - u) - c‖ = u := by
    rw [hsub, norm_neg, Real.norm_eq_abs, abs_of_pos hu_pos]
  rw [hnorm, hsub, smul_eq_mul] at hF
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hX : ‖T (c - u) - T c - -u * f'‖ < u * (|f'| / 2) := by
    have h := mul_lt_mul_of_pos_left hF hu_pos
    rwa [← mul_assoc, mul_inv_cancel₀ hu_ne, one_mul] at h
  have hfus : -u * f' = -(u * |f'|) := by rw [habs]; ring
  have hrhs : u * (|f'| / 2) = u * |f'| / 2 := by ring
  rw [hfus, hrhs] at hX
  have hle : T (c - u) - T c - -(u * |f'|) ≤
      ‖T (c - u) - T c - -(u * |f'|)‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hw : (0 : ℝ) < u * |f'| := mul_pos hu_pos (by rw [habs]; linarith)
  linarith

/-- Equilibrium existence: for `G, H, B, Ta > 0` there is an
equilibrium temperature in the open interval `(Ta, Ta + G / H)`. No
uniqueness is claimed. -/
theorem arrhenius_equilibrium_exists {G H B Ta : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) :
    ∃ T : ℝ, T ∈ Set.Ioo Ta (Ta + G / H) ∧ arrheniusRate G H B Ta T = 0 := by
  have hGH : 0 < G / H := div_pos hG hH
  have hle : Ta ≤ Ta + G / H := le_add_of_nonneg_right (le_of_lt hGH)
  have hpos : 0 < arrheniusRate G H B Ta Ta := arrheniusRate_pos_ambient hG
  have hneg : arrheniusRate G H B Ta (Ta + G / H) < 0 :=
    arrheniusRate_neg_at_upper hG hH hB hTa
  have hcont : ContinuousOn (fun T : ℝ => arrheniusRate G H B Ta T)
      (Set.Icc Ta (Ta + G / H)) := by
    have h0 : ContinuousOn (fun T : ℝ => arrheniusRate G H B Ta T) {0}ᶜ := by
      unfold arrheniusRate
      apply ContinuousOn.sub
      · apply ContinuousOn.mul continuousOn_const
        apply Real.continuous_exp.comp_continuousOn
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx
        show x ≠ 0
        simpa using hx
      · apply ContinuousOn.mul continuousOn_const
        exact ContinuousOn.sub continuousOn_id continuousOn_const
    apply h0.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hTa hx.1)
  have hmem : (0 : ℝ) ∈ Set.Ioo (arrheniusRate G H B Ta (Ta + G / H))
      (arrheniusRate G H B Ta Ta) := ⟨hneg, hpos⟩
  have himg := intermediate_value_Ioo' hle hcont hmem
  obtain ⟨T, hTmem, hTeq⟩ := himg
  exact ⟨T, hTmem, hTeq⟩

/-- Finite-horizon trapping: if `T` has within-derivative
`arrheniusRate G H B Ta (T s) / C` on `Set.Icc 0 t` at every
`s ∈ [0, t]`, with `C > 0` and `0 < T s` on the interval (the
rate is a thermal model only for positive temperatures), then
`T t` lies in `[lo, hi]` where
`lo = min (T 0) Ta` and `hi = max (T 0) (Ta + G / H)`. This
applies to any solution on the interval `[0, t]`, including a
maximal solution restricted to a compact subinterval of its
domain. -/
lemma arrhenius_solution_trapped_on_interval {G H B Ta C : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) (hC : 0 < C)
    {T : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hT : ∀ s : ℝ, s ∈ Set.Icc 0 t →
      HasDerivWithinAt T (arrheniusRate G H B Ta (T s) / C) (Set.Icc 0 t) s)
    (hpos : ∀ s : ℝ, s ∈ Set.Icc 0 t → 0 < T s) :
    T t ∈ Set.Icc (min (T 0) Ta) (max (T 0) (Ta + G / H)) := by
  have hcont : ContinuousOn T (Set.Icc 0 t) :=
    fun x hx => (hT x hx).continuousWithinAt
  have hne : (Set.Icc (0 : ℝ) t).Nonempty := Set.nonempty_Icc.mpr ht
  have hub : T t ≤ max (T 0) (Ta + G / H) := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc_mem, hc_max⟩ := IsCompact.exists_isMaxOn isCompact_Icc hne hcont
    have hc0 : c ≠ 0 := by
      intro hceq
      subst hceq
      have hle0 : T 0 ≤ max (T 0) (Ta + G / H) := le_max_left _ _
      have h2 : T t ≤ T 0 := hc_max (Set.mem_Icc.mpr ⟨ht, le_refl t⟩)
      linarith
    have hc_pos : 0 < c := lt_of_le_of_ne hc_mem.1 (Ne.symm hc0)
    have htt : T t ≤ T c := hc_max (Set.mem_Icc.mpr ⟨ht, le_refl t⟩)
    have hmax : max (T 0) (Ta + G / H) < T c := lt_of_lt_of_le hcon htt
    have hTc : Ta + G / H < T c := lt_of_le_of_lt (le_max_right _ _) hmax
    have hrate : arrheniusRate G H B Ta (T c) < 0 :=
      arrheniusRate_neg_of_gt_upper hG hH hB hTa hTc
    have hderiv := hT c hc_mem
    have hf' : arrheniusRate G H B Ta (T c) / C < 0 :=
      div_neg_of_neg_of_pos hrate hC
    obtain ⟨s, hs_mem, hsc, hlt⟩ :=
      exists_left_gt_of_hasDerivWithinAt_neg_on_interval hderiv hf' hc_pos hc_mem.2
    have hle : T s ≤ T c := hc_max hs_mem
    linarith
  have hlb : min (T 0) Ta ≤ T t := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc_mem, hc_min⟩ := IsCompact.exists_isMinOn isCompact_Icc hne hcont
    have hc0 : c ≠ 0 := by
      intro hceq
      subst hceq
      have hle0 : min (T 0) Ta ≤ T 0 := min_le_left _ _
      have h2 : T 0 ≤ T t := hc_min (Set.mem_Icc.mpr ⟨ht, le_refl t⟩)
      linarith
    have hc_pos : 0 < c := lt_of_le_of_ne hc_mem.1 (Ne.symm hc0)
    have htt : T c ≤ T t := hc_min (Set.mem_Icc.mpr ⟨ht, le_refl t⟩)
    have hmin : T c < min (T 0) Ta := lt_of_le_of_lt htt hcon
    have hTc : T c < Ta := lt_of_lt_of_le hmin (min_le_right _ _)
    have hrate : 0 < arrheniusRate G H B Ta (T c) :=
      arrheniusRate_pos_of_le_ambient hG hH (hpos c hc_mem) (le_of_lt hTc)
    have hderiv := hT c hc_mem
    have hf' : 0 < arrheniusRate G H B Ta (T c) / C := div_pos hrate hC
    obtain ⟨s, hs_mem, hsc, hlt⟩ :=
      exists_left_lt_of_hasDerivWithinAt_pos_on_interval hderiv hf' hc_pos hc_mem.2
    have hle : T c ≤ T s := hc_min hs_mem
    linarith
  exact Set.mem_Icc.mpr ⟨hlb, hub⟩

/-- Forward trapping for a forward solution defined for all
`t ≥ 0`: if `T` has within-derivative
`arrheniusRate G H B Ta (T t) / C` on `Set.Ici 0` at every
`t ≥ 0`, with `C > 0`, then `T t` lies in `[lo, hi]` where
`lo = min (T 0) Ta` and `hi = max (T 0) (Ta + G / H)`, for every
`t ≥ 0`. This is the finite-horizon trapping lemma applied on
`[0, t]`; it presupposes a solution existing for all forward
time and is not a global-existence claim. -/
lemma arrhenius_solution_trapped {G H B Ta C : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) (hC : 0 < C)
    {T : ℝ → ℝ}
    (hT : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt T (arrheniusRate G H B Ta (T s) / C) (Set.Ici 0) s)
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 < T s)
    {t : ℝ} (ht : 0 ≤ t) :
    T t ∈ Set.Icc (min (T 0) Ta) (max (T 0) (Ta + G / H)) := by
  exact arrhenius_solution_trapped_on_interval hG hH hB hTa hC ht
    (fun s hs => (hT s hs.1).mono Set.Icc_subset_Ici_self)
    (fun s hs => hpos s hs.1)

end Chemistry.CombustionAcoustics
