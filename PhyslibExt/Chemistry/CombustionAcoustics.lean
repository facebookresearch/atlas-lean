/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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

Section D treats the explicitly approximate Frank-Kamenetskii model
`θ' = δ * exp θ - θ` (dimensionless temperature excess `θ`, `δ > 0`),
which replaces the bounded Arrhenius factor by an exponential in `θ`.
A nonnegative equilibrium exists iff `δ ≤ exp (-1)`, with tangency at
`θ = 1` for `δ = exp (-1)`. The field is at least `1 + log δ`, which is
positive iff `δ > exp (-1)`; then a solution from `θ₀` in a declared
finite validity box `[a, b]` exists up to the time it reaches `b`, stays
in the box until then, and reaches `b` no later than
`(b - θ₀) / (1 + log δ)`. Nothing is claimed after the exit, and the
no-equilibrium property does not transfer to the exact law, which always
has an equilibrium (`arrhenius_equilibrium_exists`).

## ii. Key results

- `Chemistry.CombustionAcoustics.arrhenius_equilibrium_exists`: an equilibrium
  temperature exists in the stated bracket.
- `Chemistry.CombustionAcoustics.arrhenius_solution_trapped`: forward
  solutions are trapped in the stated interval.
- `Chemistry.CombustionAcoustics.hasDerivAt_acousticModeEnergy`: the
  standing-mode acoustic energy derivative (heat-release source
  minus algebraic damping), with its interval balance
  `acousticModeEnergy_sub_eq_integral`, the signed dissipation
  corollary `acousticModeEnergy_deriv_nonpos_of_no_heat`, and the
  zero-derivative case `hasDerivAt_acousticModeEnergy_conserved` and
  genuine conservation `acousticModeEnergy_eq_of_conserved`.
- `Chemistry.CombustionAcoustics.critRatio_two_folds`: for
  `B > 4 * Ta` the Semenov critical ratio `q(T) = (T - Ta) * exp (B / T)`
  has two distinct stationary points above `Ta`, both nondegenerate
  (`critRatio_two_folds_nondegenerate`); at `B = 4 * Ta` they merge
  into one degenerate fold at `2 * Ta`, and for `B < 4 * Ta` there is
  no stationary point above `Ta`.
- `Chemistry.CombustionAcoustics.exists_nonneg_fkField_eq_zero_iff`,
  `Chemistry.CombustionAcoustics.fkField_critical_tangency`: the
  Frank-Kamenetskii criticality `δ ≤ exp (-1)` and the tangency at
  `θ = 1`.
- `Chemistry.CombustionAcoustics.one_add_log_le_fkField`,
  `Chemistry.CombustionAcoustics.one_add_log_pos_iff`,
  `Chemistry.CombustionAcoustics.fk_solution_lower_bound`,
  `Chemistry.CombustionAcoustics.fk_time_le_of_le`: the supercritical
  lower bound `1 + log δ`, linear growth, and the time-in-box bound.
- `Chemistry.CombustionAcoustics.fk_exists_box_exit`: existence (local
  Picard-Lindelöf for the field frozen outside the box) and exit through
  the top of a validity box by time `(b - θ₀) / (1 + log δ)`.

## iii. Table of contents

- A. Arrhenius equilibrium and trapping
- B. Acoustic modal energy
- C. Semenov critical ratio and folds
- D. Frank-Kamenetskii criticality and box exit

## iv. References

- The sign bracket is the classical Semenov/Frank-Kamenetskii
  zeroth-order balance; the formal statement is self-contained.
- The critical-ratio fold picture of Section C is the classical
  Semenov thermal-explosion criticality (N. N. Semenov, 1928; see
  D. A. Frank-Kamenetskii, *Diffusion and Heat Transfer in Chemical
  Kinetics*, 2nd ed., Plenum, 1969, Chapter 1): with ambient
  temperature `Ta` and activation ratio `B = E / R`, equilibrium is
  `G / H = q(T)` for `q(T) = (T - Ta) * exp (B / T)`, and the two
  stationary points of `q` merge at `B = 4 * Ta`, `T = 2 * Ta`.
- Acoustic energy: A. D. Pierce, *Acoustics: An Introduction
  to Its Physical Principles and Applications* (McGraw-Hill,
  1981), Chapter 1 (acoustic energy density and energy flux
  for a progressive wave) and the duct-mode discussion of
  Chapter 7. In the notation here, a single standing duct mode
  has pressure amplitude `A` and velocity amplitude `B` linked
  by the modal equations with wavenumber `π / L`; `H` is a
  constant heat-release amplitude entering the pressure
  equation through the `(γ - 1) * H` source, and `r` is a
  linear damping coefficient in the momentum equation. The
  factor `L / 4` comes from integrating the energy density
  over the duct: `∫₀ᴸ sin²(πx/L) dx = L/2`, and the `1/2` in
  the acoustic energy density then gives `L/4`. The energy
  here is total energy per unit duct cross-section. The
  formal statement is self-contained.

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

/-! ## B. Acoustic modal energy -/

/-- Acoustic modal energy for one standing mode with pressure amplitude
`A` and velocity amplitude `B` in a duct of length `L`, ratio of
specific heats `γ`, mean pressure `pbar`, and density `ρ`:
`E = L * (A^2 / (γ * pbar) + ρ * B^2) / 4`. -/
noncomputable def acousticModeEnergy (γ pbar ρ L A B : ℝ) : ℝ :=
  L * (A ^ 2 / (γ * pbar) + ρ * B ^ 2) / 4

private lemma hasDerivAt_sq (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

private lemma hasDerivAt_const_mul' {f : ℝ → ℝ} {f' x : ℝ} (c : ℝ)
    (h : HasDerivAt f f' x) : HasDerivAt (fun y => c * f y) (c * f') x :=
  h.const_mul c

private lemma hasDerivAt_mul_const' {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) (c : ℝ) : HasDerivAt (fun y => f y * c) (f' * c) x :=
  h.mul_const c

private lemma hasDerivAt_div_const' {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) (c : ℝ) : HasDerivAt (fun y => f y / c) (f' / c) x :=
  h.div_const c

/-- Energy identity for the acoustic mode: if `A` and `B` are
differentiable in time with
`A' = -γ * pbar * (π / L) * B + (γ - 1) * H` and
`ρ * B' = (π / L) * A - r * B` (with `B'` the derivative value), then
the energy `E(t) = L * (A(t)^2 / (γ * pbar) + ρ * B(t)^2) / 4` has
derivative
`L * (γ - 1) * A(t) * H / (2 * γ * pbar) - r * L * B(t)^2 / 2`:
the heat-release source term minus the algebraic damping term
`r * L * B(t)^2 / 2` (a genuine dissipation under `0 ≤ r` and
`0 < L`; see `acousticModeEnergy_deriv_nonpos_of_no_heat`). Here `H` is a
constant heat-release amplitude for this identity. -/
lemma hasDerivAt_acousticModeEnergy
    {γ pbar ρ L r H : ℝ} (hγ : γ ≠ 0) (hpbar : pbar ≠ 0)
    (hL : L ≠ 0) {A B : ℝ → ℝ} {A' B' : ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hA' : A' = -γ * pbar * (Real.pi / L) * B t + (γ - 1) * H)
    (hB' : ρ * B' = (Real.pi / L) * A t - r * B t) :
    HasDerivAt (fun s : ℝ => acousticModeEnergy γ pbar ρ L (A s) (B s))
      (L * (γ - 1) * A t * H / (2 * γ * pbar) - r * L * B t ^ 2 / 2) t := by
  have hA2 : HasDerivAt (fun s : ℝ => A s ^ 2) ((2 * A t) * A') t :=
    (HasDerivAt.comp t (hasDerivAt_sq (A t)) hA).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have hA2d := hasDerivAt_div_const' hA2 (γ * pbar)
  have hB2 : HasDerivAt (fun s : ℝ => B s ^ 2) ((2 * B t) * B') t :=
    (HasDerivAt.comp t (hasDerivAt_sq (B t)) hB).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have hB2c := hasDerivAt_const_mul' ρ hB2
  have hsum := hA2d.add hB2c
  have hLc := hasDerivAt_const_mul' L hsum
  have hE := hasDerivAt_div_const' hLc 4
  have h1 : ρ * ((2 * B t) * B') = (2 * B t) * ((Real.pi / L) * A t - r * B t) := by
    calc ρ * ((2 * B t) * B') = (2 * B t) * (ρ * B') := by ring
      _ = (2 * B t) * ((Real.pi / L) * A t - r * B t) := by rw [hB']
  have hDF : L * ((((2 * A t) * A') / (γ * pbar)) + ρ * ((2 * B t) * B')) / 4 =
      L * (γ - 1) * A t * H / (2 * γ * pbar) - r * L * B t ^ 2 / 2 := by
    rw [hA', h1]
    have hγp : γ * pbar ≠ 0 := mul_ne_zero hγ hpbar
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have h2γp : 2 * γ * pbar ≠ 0 := mul_ne_zero (mul_ne_zero h2 hγ) hpbar
    field_simp [hγp, hL, h2γp]
    ring
  rw [hDF] at hE
  exact hE.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    simp only [acousticModeEnergy, Pi.add_apply])

/-- Signed dissipation with no heat release: under `0 ≤ r` and
`0 < L`, with `H = 0`, the modal energy derivative is
`-(r * L * B(t)^2 / 2)`, which is nonpositive. -/
lemma acousticModeEnergy_deriv_nonpos_of_no_heat
    {γ pbar ρ L r : ℝ} (hγ : γ ≠ 0) (hpbar : pbar ≠ 0)
    (hL : 0 < L) (hr : 0 ≤ r) {A B : ℝ → ℝ} {A' B' : ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hA' : A' = -γ * pbar * (Real.pi / L) * B t + (γ - 1) * 0)
    (hB' : ρ * B' = (Real.pi / L) * A t - r * B t) :
    HasDerivAt (fun s : ℝ => acousticModeEnergy γ pbar ρ L (A s) (B s))
        (-(r * L * B t ^ 2 / 2)) t ∧ -(r * L * B t ^ 2 / 2) ≤ 0 := by
  have h := hasDerivAt_acousticModeEnergy (r := r) (H := 0) hγ hpbar
    (ne_of_gt hL) hA hB hA' hB'
  have e : L * (γ - 1) * A t * 0 / (2 * γ * pbar) - r * L * B t ^ 2 / 2
      = -(r * L * B t ^ 2 / 2) := by ring
  rw [e] at h
  refine ⟨h, ?_⟩
  have hnn : (0 : ℝ) ≤ r * L * B t ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hr (le_of_lt hL)) (sq_nonneg _)) (by norm_num)
  linarith

/-- Integrated energy balance over a time interval `[t0, t1]`: under
the same modal equations at every time, the energy change equals the
integral of the heat-release source minus the algebraic
damping term. -/
lemma acousticModeEnergy_sub_eq_integral
    {γ pbar ρ L r H : ℝ} (hγ : 0 < γ) (hpbar : 0 < pbar)
    (hL : 0 < L) {A B A' B' : ℝ → ℝ} (t0 t1 : ℝ)
    (hA : ∀ t ∈ Set.uIcc t0 t1, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ Set.uIcc t0 t1, HasDerivAt B (B' t) t)
    (hA' : ∀ t ∈ Set.uIcc t0 t1,
      A' t = -γ * pbar * (Real.pi / L) * B t + (γ - 1) * H)
    (hB' : ∀ t ∈ Set.uIcc t0 t1,
      ρ * B' t = (Real.pi / L) * A t - r * B t) :
    acousticModeEnergy γ pbar ρ L (A t1) (B t1) -
        acousticModeEnergy γ pbar ρ L (A t0) (B t0) =
      ∫ t in t0..t1,
        (L * (γ - 1) * A t * H / (2 * γ * pbar) - r * L * B t ^ 2 / 2) := by
  have hγ' : γ ≠ 0 := ne_of_gt hγ
  have hpbar' : pbar ≠ 0 := ne_of_gt hpbar
  have hL' : L ≠ 0 := ne_of_gt hL
  have hderiv : ∀ x ∈ Set.uIcc t0 t1,
      HasDerivAt (fun s : ℝ => acousticModeEnergy γ pbar ρ L (A s) (B s))
        (L * (γ - 1) * A x * H / (2 * γ * pbar) - r * L * B x ^ 2 / 2) x :=
    fun x hx => hasDerivAt_acousticModeEnergy hγ' hpbar' hL'
      (hA x hx) (hB x hx) (hA' x hx) (hB' x hx)
  have hAcont : ContinuousOn A (Set.uIcc t0 t1) :=
    fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hBcont : ContinuousOn B (Set.uIcc t0 t1) :=
    fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ =>
      L * (γ - 1) * A t * H / (2 * γ * pbar) - r * L * B t ^ 2 / 2)
      (Set.uIcc t0 t1) := by
    have e1 : ContinuousOn (fun t : ℝ => L * (γ - 1) * A t * H / (2 * γ * pbar))
        (Set.uIcc t0 t1) :=
      ((hAcont.const_mul (L * (γ - 1))).mul_const H).div_const (2 * γ * pbar)
    have e2 : ContinuousOn (fun t : ℝ => r * L * B t ^ 2 / 2)
        (Set.uIcc t0 t1) :=
      ((hBcont.pow 2).const_mul (r * L)).div_const 2
    exact e1.sub e2
  have hint : IntervalIntegrable (fun t : ℝ =>
      L * (γ - 1) * A t * H / (2 * γ * pbar) - r * L * B t ^ 2 / 2)
      MeasureTheory.volume t0 t1 := hcont.intervalIntegrable
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm

/-- With no heat release and no dissipation, the modal energy has
zero derivative at any single time satisfying the modal equations.
Genuine conservation between two times is
`acousticModeEnergy_eq_of_conserved`. -/
lemma hasDerivAt_acousticModeEnergy_conserved
    {γ pbar ρ L : ℝ} (hγ : γ ≠ 0) (hpbar : pbar ≠ 0)
    (hL : L ≠ 0) {A B : ℝ → ℝ} {A' B' : ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hA' : A' = -γ * pbar * (Real.pi / L) * B t)
    (hB' : ρ * B' = (Real.pi / L) * A t) :
    HasDerivAt (fun s : ℝ => acousticModeEnergy γ pbar ρ L (A s) (B s)) 0 t := by
  have hA0 : A' = -γ * pbar * (Real.pi / L) * B t + (γ - 1) * 0 := by
    rw [hA']; ring
  have hB0 : ρ * B' = (Real.pi / L) * A t - 0 * B t := by
    rw [hB']; ring
  have h := hasDerivAt_acousticModeEnergy (r := 0) (H := 0) hγ hpbar hL hA hB hA0 hB0
  have e : L * (γ - 1) * A t * 0 / (2 * γ * pbar) - 0 * L * B t ^ 2 / 2 = 0 := by
    ring
  rw [e] at h
  exact h

/-- Genuine conservation: if the modal equations with no heat
release (`H = 0`) and no damping (`r = 0`) hold at every time, the
modal energy takes the same value at any two times. -/
theorem acousticModeEnergy_eq_of_conserved
    {γ pbar ρ L : ℝ} (hγ : 0 < γ) (hpbar : 0 < pbar)
    (hL : 0 < L) {A B A' B' : ℝ → ℝ}
    (hA : ∀ t : ℝ, HasDerivAt A (A' t) t)
    (hB : ∀ t : ℝ, HasDerivAt B (B' t) t)
    (hA' : ∀ t : ℝ, A' t = -γ * pbar * (Real.pi / L) * B t)
    (hB' : ∀ t : ℝ, ρ * B' t = (Real.pi / L) * A t)
    (t0 t1 : ℝ) :
    acousticModeEnergy γ pbar ρ L (A t1) (B t1) =
      acousticModeEnergy γ pbar ρ L (A t0) (B t0) := by
  have h := acousticModeEnergy_sub_eq_integral (r := 0) (H := 0)
    hγ hpbar hL t0 t1
    (fun t _ => hA t) (fun t _ => hB t)
    (fun t _ => by rw [hA' t]; ring)
    (fun t _ => by rw [hB' t]; ring)
  have hzero : (∫ t in t0..t1,
      (L * (γ - 1) * A t * 0 / (2 * γ * pbar) -
        0 * L * B t ^ 2 / 2)) = 0 := by simp
  rw [hzero] at h
  exact sub_eq_zero.mp h

/-! ## C. Semenov critical ratio and folds -/

/-- Semenov critical ratio `q(T) = (T - Ta) * exp(B / T)`: for
`H, T > 0`, equilibrium of the Arrhenius rate is `G / H = q(T)`. -/
noncomputable def critRatio (Ta B T : ℝ) : ℝ :=
  (T - Ta) * Real.exp (B / T)

private lemma critRatio_hasDerivAt_const_div {B T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun T : ℝ => B / T) (-B / T ^ 2) T := by
  have h := HasDerivAt.div (hasDerivAt_const T B) (hasDerivAt_id' T) (ne_of_gt hT)
  have e : (0 * T - B * 1) / T ^ 2 = -B / T ^ 2 := by ring
  rwa [e] at h

private lemma critRatio_hasDerivAt_sq {T : ℝ} :
    HasDerivAt (fun s : ℝ => s ^ 2) (2 * T) T :=
  hasDerivAt_sq T

private lemma critRatio_hasDerivAt_inv {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun s : ℝ => s⁻¹) (-1 / T ^ 2) T := by
  have h := hasDerivAt_inv (ne_of_gt hT)
  have e : (-(T ^ 2)⁻¹) = -1 / T ^ 2 := by rw [← one_div, ← neg_div]
  rwa [e] at h

private lemma critRatio_hasDerivAt_inv_sq {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹)
      ((-1 / T ^ 2) * T⁻¹ + T⁻¹ * (-1 / T ^ 2)) T := by
  have hInv : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / T ^ 2) T :=
    critRatio_hasDerivAt_inv hT
  have hmul : HasDerivAt (fun s : ℝ => s⁻¹ * s⁻¹)
      ((-1 / T ^ 2) * T⁻¹ + T⁻¹ * (-1 / T ^ 2)) T :=
    hInv.mul hInv
  have heq : (fun s : ℝ => (s ^ 2)⁻¹) =ᶠ[nhds T]
      (fun s : ℝ => s⁻¹ * s⁻¹) := by
    apply Filter.Eventually.of_forall
    intro s
    show (s ^ 2)⁻¹ = s⁻¹ * s⁻¹
    rw [← inv_pow]
    ring
  exact hmul.congr_of_eventuallyEq heq

/-- Equilibrium is the critical-ratio equation: for `0 < H` and
`0 < T`, `arrheniusRate G H B Ta T = 0 ↔ G / H = critRatio Ta B T`. -/
lemma equilibrium_iff_critRatio {G H B Ta T : ℝ} (hH : 0 < H)
    (hT : 0 < T) :
    arrheniusRate G H B Ta T = 0 ↔ G / H = critRatio Ta B T := by
  have hH' : H ≠ 0 := ne_of_gt hH
  have _ : T ≠ 0 := ne_of_gt hT
  have hexp : -B / T + B / T = 0 := by ring
  have he : Real.exp (-B / T) * Real.exp (B / T) = 1 := by
    rw [← Real.exp_add, hexp, Real.exp_zero]
  have he' : Real.exp (B / T) * Real.exp (-B / T) = 1 := by
    rw [mul_comm]; exact he
  unfold arrheniusRate critRatio
  rw [div_eq_iff hH']
  constructor
  · intro h
    have h1 : G * Real.exp (-B / T) = H * (T - Ta) := by linarith [h]
    calc G = G * (Real.exp (-B / T) * Real.exp (B / T)) := by rw [he]; ring
      _ = (G * Real.exp (-B / T)) * Real.exp (B / T) := by ring
      _ = (H * (T - Ta)) * Real.exp (B / T) := by rw [h1]
      _ = (T - Ta) * Real.exp (B / T) * H := by ring
  · intro h
    have h2 : G * Real.exp (-B / T) = H * (T - Ta) := by
      calc G * Real.exp (-B / T)
          = ((T - Ta) * Real.exp (B / T) * H) * Real.exp (-B / T) := by rw [h]
        _ = H * (T - Ta) * (Real.exp (B / T) * Real.exp (-B / T)) := by ring
        _ = H * (T - Ta) := by rw [he']; ring
    linarith [h2]

/-- Derivative of the critical ratio for `T > 0`:
`q'(T) = exp(B / T) * (T^2 - B * T + B * Ta) / T^2`. -/
lemma critRatio_hasDerivAt {Ta B T : ℝ} (hT : 0 < T) :
    HasDerivAt (critRatio Ta B)
      (Real.exp (B / T) * (T ^ 2 - B * T + B * Ta) / T ^ 2) T := by
  have hT' : T ≠ 0 := ne_of_gt hT
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hT2' : T ^ 2 ≠ 0 := ne_of_gt hT2
  have hBT : HasDerivAt (fun T : ℝ => B / T) (-B / T ^ 2) T :=
    critRatio_hasDerivAt_const_div hT
  have hexp : HasDerivAt (fun T : ℝ => Real.exp (B / T))
      (Real.exp (B / T) * (-B / T ^ 2)) T := hBT.exp
  have hu : HasDerivAt (fun T : ℝ => T - Ta) ((1 : ℝ) - 0) T :=
    (hasDerivAt_id T).sub (hasDerivAt_const T Ta)
  rw [sub_zero] at hu
  have hmul : HasDerivAt (fun T : ℝ => (T - Ta) * Real.exp (B / T))
      (1 * Real.exp (B / T) + (T - Ta) * (Real.exp (B / T) * (-B / T ^ 2))) T :=
    hu.mul hexp
  have hval : 1 * Real.exp (B / T) + (T - Ta) * (Real.exp (B / T) * (-B / T ^ 2))
      = Real.exp (B / T) * (T ^ 2 - B * T + B * Ta) / T ^ 2 := by
    field_simp
    ring
  rw [hval] at hmul
  exact hmul

/-- For `T > Ta > 0`, the critical ratio is stationary exactly at
the roots of `T^2 - B * T + B * Ta = 0`. -/
lemma critRatio_deriv_eq_zero_iff {Ta B T : ℝ} (hTa : 0 < Ta)
    (hT : Ta < T) :
    deriv (critRatio Ta B) T = 0 ↔ T ^ 2 - B * T + B * Ta = 0 := by
  have hTpos : 0 < T := lt_trans hTa hT
  have hderiv := (critRatio_hasDerivAt (Ta := Ta) (B := B) hTpos).deriv
  rw [hderiv]
  have hexp : Real.exp (B / T) ≠ 0 := (Real.exp_pos _).ne'
  have hT2pos : (0 : ℝ) < T ^ 2 := by positivity
  have hT2 : (T : ℝ) ^ 2 ≠ 0 := ne_of_gt hT2pos
  simp only [div_eq_zero_iff, mul_eq_zero, hexp, hT2, or_false, false_or]

/-- Two ordinary folds: for `0 < Ta` and `B > 4 * Ta`, the two
temperatures `T± = (B ± √(B^2 - 4 * B * Ta)) / 2` are distinct,
both exceed `Ta`, ordered `Ta < T- < T+`, and both are stationary
points of the critical ratio. -/
theorem critRatio_two_folds {Ta B : ℝ} (hTa : 0 < Ta)
    (hB : 4 * Ta < B) :
    deriv (critRatio Ta B) ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) = 0 ∧
    deriv (critRatio Ta B) ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) = 0 ∧
    Ta < (B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 ∧
    (B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 <
      (B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 := by
  have h4Ta : (0 : ℝ) < 4 * Ta := by linarith [hTa]
  have hBpos : 0 < B := lt_trans h4Ta hB
  have hB4 : (0 : ℝ) < B - 4 * Ta := sub_pos.mpr hB
  have hD : (0 : ℝ) < B ^ 2 - 4 * B * Ta := by
    have e : B ^ 2 - 4 * B * Ta = B * (B - 4 * Ta) := by ring
    rw [e]
    exact mul_pos hBpos hB4
  have hs : (0 : ℝ) < Real.sqrt (B ^ 2 - 4 * B * Ta) := Real.sqrt_pos.mpr hD
  have hsq : Real.sqrt (B ^ 2 - 4 * B * Ta) ^ 2 = B ^ 2 - 4 * B * Ta :=
    Real.sq_sqrt hD.le
  have hB2 : (0 : ℝ) < B - 2 * Ta := by linarith [hB, hTa]
  have hsq_lt : Real.sqrt (B ^ 2 - 4 * B * Ta) < B - 2 * Ta := by
    rw [Real.sqrt_lt' hB2]
    have e : B ^ 2 - 4 * B * Ta = (B - 2 * Ta) ^ 2 - 4 * Ta ^ 2 := by ring
    have h4T : (0 : ℝ) < 4 * Ta ^ 2 := by positivity
    rw [e]
    linarith [h4T]
  have hTm : Ta < (B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 := by
    linarith [hsq_lt]
  have hord : (B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2
      < (B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 := by linarith [hs]
  have hTp : Ta < (B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 :=
    lt_trans hTm hord
  have hQm : ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
      - B * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta = 0 := by
    have e : ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
        - B * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta
        = (Real.sqrt (B ^ 2 - 4 * B * Ta) ^ 2 - (B ^ 2 - 4 * B * Ta)) / 4 := by
      ring
    rw [e, hsq]
    ring
  have hQp : ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
      - B * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta = 0 := by
    have e : ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
        - B * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta
        = (Real.sqrt (B ^ 2 - 4 * B * Ta) ^ 2 - (B ^ 2 - 4 * B * Ta)) / 4 := by
      ring
    rw [e, hsq]
    ring
  have hdm := (critRatio_deriv_eq_zero_iff hTa hTm).mpr hQm
  have hdp := (critRatio_deriv_eq_zero_iff hTa hTp).mpr hQp
  exact ⟨hdm, hdp, hTm, hord⟩

/-- Degenerate fold: at `B = 4 * Ta` there is exactly one stationary
point above `Ta`, at `T = 2 * Ta`; it is not two ordinary folds. -/
theorem critRatio_degenerate_fold {Ta : ℝ} (hTa : 0 < Ta) {T : ℝ}
    (hT : Ta < T) :
    deriv (critRatio Ta (4 * Ta)) T = 0 ↔ T = 2 * Ta := by
  have hiff :=
    critRatio_deriv_eq_zero_iff (B := 4 * Ta) hTa hT
  rw [hiff]
  have e : T ^ 2 - 4 * Ta * T + 4 * Ta * Ta = (T - 2 * Ta) ^ 2 := by ring
  rw [e, sq_eq_zero_iff, sub_eq_zero]

/-- No critical point: for `B < 4 * Ta`, the critical ratio has no
stationary point above `Ta`. (Algebraically,
`T^2 - B * T + B * Ta = (T - 2 * Ta)^2 + (T - Ta) * (4 * Ta - B)`.) -/
theorem critRatio_no_critical_of_lt {Ta B : ℝ} (hTa : 0 < Ta)
    (hB : B < 4 * Ta) {T : ℝ} (hT : Ta < T) :
    deriv (critRatio Ta B) T ≠ 0 := by
  have hiff := critRatio_deriv_eq_zero_iff (B := B) hTa hT
  intro h
  rw [hiff] at h
  have e : T ^ 2 - B * T + B * Ta
      = (T - 2 * Ta) ^ 2 + (T - Ta) * (4 * Ta - B) := by ring
  rw [e] at h
  have hpos1 : (0 : ℝ) ≤ (T - 2 * Ta) ^ 2 := sq_nonneg _
  have hpos2 : (0 : ℝ) < (T - Ta) * (4 * Ta - B) :=
    mul_pos (sub_pos.mpr hT) (sub_pos.mpr hB)
  have hpos : (0 : ℝ) < (T - 2 * Ta) ^ 2 + (T - Ta) * (4 * Ta - B) :=
    add_pos_of_nonneg_of_pos hpos1 hpos2
  exact absurd h (ne_of_gt hpos)

/-- At a stationary point the derivative function
`s ↦ exp (B / s) * (s^2 - B * s + B * Ta) / s^2` (which agrees with
`deriv (critRatio Ta B)` at every positive point) has derivative
`exp (B / T) * (2 * T - B) / T^2`: the terms containing the
vanishing polynomial drop out. -/
lemma critRatio_deriv_hasDerivAt_at_root {Ta B T : ℝ} (hT : 0 < T)
    (hP : T ^ 2 - B * T + B * Ta = 0) :
    HasDerivAt (fun s : ℝ => Real.exp (B / s) * (s ^ 2 - B * s + B * Ta) / s ^ 2)
      (Real.exp (B / T) * (2 * T - B) / T ^ 2) T := by
  have hT' : T ≠ 0 := ne_of_gt hT
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hT2' : T ^ 2 ≠ 0 := ne_of_gt hT2
  have hBT : HasDerivAt (fun s : ℝ => B / s) (-B / T ^ 2) T :=
    critRatio_hasDerivAt_const_div hT
  have hE : HasDerivAt (fun s : ℝ => Real.exp (B / s))
      (Real.exp (B / T) * (-B / T ^ 2)) T := hBT.exp
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * T) T := critRatio_hasDerivAt_sq
  have hBs : HasDerivAt (fun s : ℝ => B * s) B T := by
    have h := HasDerivAt.const_mul B (hasDerivAt_id' T)
    have hval : B * (1 : ℝ) = B := by ring
    rw [hval] at h
    exact h
  have hsub : HasDerivAt (fun s : ℝ => s ^ 2 - B * s) (2 * T - B) T :=
    hsq.sub hBs
  have hconst : HasDerivAt (fun _ : ℝ => B * Ta) (0 : ℝ) T :=
    hasDerivAt_const T (B * Ta)
  have hPderiv : HasDerivAt (fun s : ℝ => s ^ 2 - B * s + B * Ta) (2 * T - B) T := by
    have hadd := hsub.add hconst
    have hval : (2 * T - B) + (0 : ℝ) = 2 * T - B := by ring
    rw [hval] at hadd
    exact hadd
  have hN : HasDerivAt (fun s : ℝ => Real.exp (B / s) * (s ^ 2 - B * s + B * Ta))
      ((Real.exp (B / T) * (-B / T ^ 2)) * (T ^ 2 - B * T + B * Ta)
        + Real.exp (B / T) * (2 * T - B)) T :=
    hE.mul hPderiv
  have hI := critRatio_hasDerivAt_inv_sq hT
  have hG : HasDerivAt
      (fun s : ℝ => (Real.exp (B / s) * (s ^ 2 - B * s + B * Ta)) * (s ^ 2)⁻¹)
      (((Real.exp (B / T) * (-B / T ^ 2)) * (T ^ 2 - B * T + B * Ta)
        + Real.exp (B / T) * (2 * T - B)) * (T ^ 2)⁻¹
        + (Real.exp (B / T) * (T ^ 2 - B * T + B * Ta))
          * ((-1 / T ^ 2) * T⁻¹ + T⁻¹ * (-1 / T ^ 2))) T :=
    hN.mul hI
  have heq : (fun s : ℝ => Real.exp (B / s) * (s ^ 2 - B * s + B * Ta) / s ^ 2)
      =ᶠ[nhds T]
      (fun s : ℝ => (Real.exp (B / s) * (s ^ 2 - B * s + B * Ta)) * (s ^ 2)⁻¹) := by
    apply Filter.Eventually.of_forall
    intro s
    show Real.exp (B / s) * (s ^ 2 - B * s + B * Ta) / s ^ 2
      = (Real.exp (B / s) * (s ^ 2 - B * s + B * Ta)) * (s ^ 2)⁻¹
    rw [div_eq_mul_inv]
  have hGdiv := hG.congr_of_eventuallyEq heq
  have hval : ((Real.exp (B / T) * (-B / T ^ 2)) * (T ^ 2 - B * T + B * Ta)
        + Real.exp (B / T) * (2 * T - B)) * (T ^ 2)⁻¹
        + (Real.exp (B / T) * (T ^ 2 - B * T + B * Ta))
          * ((-1 / T ^ 2) * T⁻¹ + T⁻¹ * (-1 / T ^ 2))
      = Real.exp (B / T) * (2 * T - B) / T ^ 2 := by
    rw [hP]
    field_simp
    ring
  rw [hval] at hGdiv
  exact hGdiv

/-- The two ordinary folds are nondegenerate: the second
derivative of the critical ratio is nonzero at both fold
temperatures (it equals `exp (B / T±) * (±√(B^2 - 4 * B * Ta)) /
T±^2`). -/
theorem critRatio_two_folds_nondegenerate {Ta B : ℝ} (hTa : 0 < Ta)
    (hB : 4 * Ta < B) :
    deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ≠ 0 ∧
    deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ≠ 0 := by
  obtain ⟨hdm, hdp, hTm, hord⟩ := critRatio_two_folds hTa hB
  have hTp : Ta < (B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 :=
    lt_trans hTm hord
  have hQm : ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
      - B * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta = 0 :=
    (critRatio_deriv_eq_zero_iff hTa hTm).mp hdm
  have hQp : ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2
      - B * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) + B * Ta = 0 :=
    (critRatio_deriv_eq_zero_iff hTa hTp).mp hdp
  have hTmPos : 0 < (B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 :=
    lt_trans hTa hTm
  have hTpPos : 0 < (B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2 :=
    lt_trans hTa hTp
  have h4Ta : (0 : ℝ) < 4 * Ta := by linarith [hTa]
  have hBpos : 0 < B := lt_trans h4Ta hB
  have hB4 : (0 : ℝ) < B - 4 * Ta := sub_pos.mpr hB
  have hD : (0 : ℝ) < B ^ 2 - 4 * B * Ta := by
    have e : B ^ 2 - 4 * B * Ta = B * (B - 4 * Ta) := by ring
    rw [e]
    exact mul_pos hBpos hB4
  have hs : (0 : ℝ) < Real.sqrt (B ^ 2 - 4 * B * Ta) := Real.sqrt_pos.mpr hD
  have hHm := critRatio_deriv_hasDerivAt_at_root hTmPos hQm
  have hEvtM : (fun s : ℝ => deriv (critRatio Ta B) s)
      =ᶠ[nhds ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)]
      (fun s : ℝ => Real.exp (B / s) * (s ^ 2 - B * s + B * Ta) / s ^ 2) := by
    have hPos : ∀ᶠ s in nhds ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2), 0 < s :=
      isOpen_Ioi.eventually_mem hTmPos
    refine hPos.mono (fun s hs0 => ?_)
    exact (critRatio_hasDerivAt (Ta := Ta) (B := B) hs0).deriv
  have hHm' := hHm.congr_of_eventuallyEq hEvtM
  have hDerivM : deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)
      = Real.exp (B / ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2))
        * (2 * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B)
        / (((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2) := hHm'.deriv
  have eM : 2 * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B
      = -Real.sqrt (B ^ 2 - 4 * B * Ta) := by ring
  have h2Tm : 2 * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B ≠ 0 := by
    rw [eM]
    exact neg_ne_zero.mpr (ne_of_gt hs)
  have hexpM : Real.exp (B / ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hT2M : (((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2 : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2 := by
      positivity
    exact ne_of_gt hpos
  have hNeM : Real.exp (B / ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2))
        * (2 * ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B)
        / (((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero hexpM h2Tm) hT2M
  have hConM : deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B - Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ≠ 0 := by
    rw [hDerivM]
    exact hNeM
  have hHp := critRatio_deriv_hasDerivAt_at_root hTpPos hQp
  have hEvtP : (fun s : ℝ => deriv (critRatio Ta B) s)
      =ᶠ[nhds ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)]
      (fun s : ℝ => Real.exp (B / s) * (s ^ 2 - B * s + B * Ta) / s ^ 2) := by
    have hPos : ∀ᶠ s in nhds ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2), 0 < s :=
      isOpen_Ioi.eventually_mem hTpPos
    refine hPos.mono (fun s hs0 => ?_)
    exact (critRatio_hasDerivAt (Ta := Ta) (B := B) hs0).deriv
  have hHp' := hHp.congr_of_eventuallyEq hEvtP
  have hDerivP : deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)
      = Real.exp (B / ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2))
        * (2 * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B)
        / (((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2) := hHp'.deriv
  have eP : 2 * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B
      = Real.sqrt (B ^ 2 - 4 * B * Ta) := by ring
  have h2Tp : 2 * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B ≠ 0 := by
    rw [eP]
    exact ne_of_gt hs
  have hexpP : Real.exp (B / ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2)) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hT2P : (((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2 : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2 := by
      positivity
    exact ne_of_gt hpos
  have hNeP : Real.exp (B / ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2))
        * (2 * ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) - B)
        / (((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero hexpP h2Tp) hT2P
  have hConP : deriv (fun s : ℝ => deriv (critRatio Ta B) s)
        ((B + Real.sqrt (B ^ 2 - 4 * B * Ta)) / 2) ≠ 0 := by
    rw [hDerivP]
    exact hNeP
  exact ⟨hConM, hConP⟩

/-- The degenerate fold is degenerate: at `B = 4 * Ta` the second
derivative of the critical ratio vanishes at `T = 2 * Ta`. -/
theorem critRatio_degenerate_fold_second {Ta : ℝ} (hTa : 0 < Ta) :
    deriv (fun s : ℝ => deriv (critRatio Ta (4 * Ta)) s) (2 * Ta) = 0 := by
  have hPos : 0 < 2 * Ta := by linarith [hTa]
  have hP : (2 * Ta) ^ 2 - (4 * Ta) * (2 * Ta) + (4 * Ta) * Ta = 0 := by ring
  have hH := critRatio_deriv_hasDerivAt_at_root (Ta := Ta) (B := 4 * Ta) hPos hP
  have hEvt : (fun s : ℝ => deriv (critRatio Ta (4 * Ta)) s)
      =ᶠ[nhds (2 * Ta)]
      (fun s : ℝ => Real.exp ((4 * Ta) / s) * (s ^ 2 - (4 * Ta) * s + (4 * Ta) * Ta)
        / s ^ 2) := by
    have hPosEvt : ∀ᶠ s in nhds (2 * Ta), 0 < s :=
      isOpen_Ioi.eventually_mem hPos
    refine hPosEvt.mono (fun s hs0 => ?_)
    exact (critRatio_hasDerivAt (Ta := Ta) (B := 4 * Ta) hs0).deriv
  have hH' := hH.congr_of_eventuallyEq hEvt
  have hDeriv : deriv (fun s : ℝ => deriv (critRatio Ta (4 * Ta)) s) (2 * Ta)
      = Real.exp ((4 * Ta) / (2 * Ta)) * (2 * (2 * Ta) - 4 * Ta) / (2 * Ta) ^ 2 :=
    hH'.deriv
  have e : 2 * (2 * Ta) - 4 * Ta = 0 := by ring
  have hval : Real.exp ((4 * Ta) / (2 * Ta)) * (2 * (2 * Ta) - 4 * Ta)
      / (2 * Ta) ^ 2 = 0 := by
    rw [e]
    simp
  rw [hDeriv]
  exact hval

/-! ## D. Frank-Kamenetskii criticality and box exit -/

/-- Frank-Kamenetskii exponential-approximation field `δ * exp θ - θ`: heat release
`δ * exp θ` minus linear cooling `θ`, in dimensionless temperature excess `θ`. An approximate
model, not the exact Arrhenius law. -/
noncomputable def fkField (δ θ : ℝ) : ℝ := δ * Real.exp θ - θ

/-- Criticality: for `δ > 0` the model has a nonnegative equilibrium iff `δ ≤ exp (-1)`. -/
lemma exists_nonneg_fkField_eq_zero_iff {δ : ℝ} (hδ : 0 < δ) :
    (∃ θ : ℝ, 0 ≤ θ ∧ fkField δ θ = 0) ↔ δ ≤ Real.exp (-1) := by
  constructor
  · rintro ⟨θ, hθnn, h0⟩
    have hexp : δ * Real.exp θ = Real.exp (θ + Real.log δ) := by
      rw [Real.exp_add, Real.exp_log hδ, mul_comm]
    have h := Real.add_one_le_exp (θ + Real.log δ)
    have hlog : Real.log δ ≤ -1 := by
      have h0' : δ * Real.exp θ - θ = 0 := h0
      linarith
    have hle : Real.log δ ≤ Real.log (Real.exp (-1)) := by
      rw [Real.log_exp]
      exact hlog
    exact (Real.log_le_log_iff hδ (Real.exp_pos _)).mp hle
  · intro hle
    have h0pos : 0 < fkField δ 0 := by
      have heq : fkField δ 0 = δ := by
        change δ * Real.exp 0 - 0 = δ
        rw [Real.exp_zero, mul_one, sub_zero]
      rw [heq]
      exact hδ
    have h1 : fkField δ 1 ≤ 0 := by
      have hmul : δ * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hle (le_of_lt (Real.exp_pos 1))
      have hexp1 : Real.exp (-1) * Real.exp 1 = 1 := by
        have e : (-1 : ℝ) + 1 = 0 := by norm_num
        calc Real.exp (-1) * Real.exp 1 = Real.exp ((-1 : ℝ) + 1) := (Real.exp_add _ _).symm
          _ = Real.exp 0 := by rw [e]
          _ = 1 := Real.exp_zero
      change δ * Real.exp 1 - 1 ≤ 0
      linarith
    rcases eq_or_lt_of_le h1 with h1eq | h1lt
    · exact ⟨1, zero_le_one, h1eq⟩
    · have hcont : ContinuousOn (fkField δ) (Set.Icc 0 1) := by
        change ContinuousOn (fun u => δ * Real.exp u - u) (Set.Icc 0 1)
        exact ((continuous_const.mul Real.continuous_exp).sub continuous_id).continuousOn
      have hmem : (0 : ℝ) ∈ Set.Ioo (fkField δ 1) (fkField δ 0) := ⟨h1lt, h0pos⟩
      have himg := intermediate_value_Ioo' zero_le_one hcont hmem
      obtain ⟨θ, hθmem, hθeq⟩ := himg
      exact ⟨θ, le_of_lt hθmem.1, hθeq⟩

/-- Tangency at the critical value `δ = exp (-1)`: the field and its derivative vanish at
`θ = 1`, and `θ = 1` is the only equilibrium. -/
lemma fkField_critical_tangency :
    fkField (Real.exp (-1)) 1 = 0 ∧ HasDerivAt (fkField (Real.exp (-1))) 0 1 ∧
      ∀ θ : ℝ, fkField (Real.exp (-1)) θ = 0 → θ = 1 := by
  have hexp1 : Real.exp (-1) * Real.exp 1 = 1 := by
    have e : (-1 : ℝ) + 1 = 0 := by norm_num
    calc Real.exp (-1) * Real.exp 1 = Real.exp ((-1 : ℝ) + 1) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by rw [e]
      _ = 1 := Real.exp_zero
  refine ⟨?_, ?_, ?_⟩
  · change Real.exp (-1) * Real.exp 1 - 1 = 0
    linarith
  · have h := HasDerivAt.sub
      (HasDerivAt.const_mul (Real.exp (-1)) (Real.hasDerivAt_exp 1)) (hasDerivAt_id 1)
    have hval : Real.exp (-1) * Real.exp 1 - 1 = 0 := by linarith
    rw [hval] at h
    exact h
  · intro θ hθ
    have hθpos : 0 < θ := by
      have hpos : 0 < Real.exp (-1) * Real.exp θ := mul_pos (Real.exp_pos _) (Real.exp_pos _)
      have h0' : Real.exp (-1) * Real.exp θ - θ = 0 := hθ
      linarith
    have hexp : Real.exp (θ - 1) = θ := by
      have e : Real.exp (θ - 1) = Real.exp (-1) * Real.exp θ := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      have h0' : Real.exp (-1) * Real.exp θ - θ = 0 := hθ
      linarith
    have hderiv : ∀ w : ℝ, deriv (fun u : ℝ => Real.exp u - u) w = Real.exp w - 1 := by
      intro w
      have h := HasDerivAt.sub (Real.hasDerivAt_exp w) (hasDerivAt_id w)
      have h' : HasDerivAt (fun u : ℝ => Real.exp u - u) (Real.exp w - 1) w := h
      exact h'.deriv
    have hcont : ∀ D : Set ℝ, ContinuousOn (fun u : ℝ => Real.exp u - u) D :=
      fun D => (Real.continuous_exp.sub continuous_id).continuousOn
    have hanti : StrictAntiOn (fun u : ℝ => Real.exp u - u) (Set.Iic 0) := by
      apply strictAntiOn_of_deriv_neg (convex_Iic 0) (hcont _)
      intro x hx
      rw [interior_Iic] at hx
      rw [hderiv]
      have hlt : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
      linarith
    have hmono : StrictMonoOn (fun u : ℝ => Real.exp u - u) (Set.Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0) (hcont _)
      intro x hx
      rw [interior_Ici] at hx
      rw [hderiv]
      have hlt : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
      linarith
    have hstrict : ∀ u : ℝ, u ≠ 0 → u + 1 < Real.exp u := by
      intro u hu
      rcases lt_or_gt_of_ne hu with h | h
      · have h2 := hanti (show u ∈ Set.Iic 0 from le_of_lt h)
          (show (0 : ℝ) ∈ Set.Iic 0 from (le_rfl : (0 : ℝ) ≤ 0)) h
        simp only [Real.exp_zero, sub_zero] at h2
        linarith
      · have h2 := hmono (show (0 : ℝ) ∈ Set.Ici 0 from (le_rfl : (0 : ℝ) ≤ 0))
          (show u ∈ Set.Ici 0 from le_of_lt h) h
        simp only [Real.exp_zero, sub_zero] at h2
        linarith
    have hu : θ - 1 = 0 := by
      by_contra hne
      have hlt := hstrict (θ - 1) hne
      rw [hexp] at hlt
      linarith
    linarith

/-- Uniform lower bound: for `δ > 0` the field is at least `1 + log δ` everywhere. -/
lemma one_add_log_le_fkField {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) :
    1 + Real.log δ ≤ fkField δ θ := by
  have hexp : δ * Real.exp θ = Real.exp (θ + Real.log δ) := by
    rw [Real.exp_add, Real.exp_log hδ, mul_comm]
  have h := Real.add_one_le_exp (θ + Real.log δ)
  change 1 + Real.log δ ≤ δ * Real.exp θ - θ
  linarith

/-- The bound is positive exactly in the supercritical range `δ > exp (-1)`. -/
lemma one_add_log_pos_iff {δ : ℝ} (hδ : 0 < δ) :
    0 < 1 + Real.log δ ↔ Real.exp (-1) < δ := by
  rw [← Real.lt_log_iff_exp_lt hδ]
  constructor <;> intro h <;> linarith

/-- Lower growth bound: a solution of `θ' = δ * exp θ - θ` on `[0, t]`, `δ > 0`, gains at
least `(1 + log δ) * t`. -/
lemma fk_solution_lower_bound {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) {θ : ℝ → ℝ}
    (hθ : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt θ (fkField δ (θ s)) (Set.Icc 0 t) s) :
    θ 0 + (1 + Real.log δ) * t ≤ θ t := by
  have hθcont : ContinuousOn θ (Set.Icc 0 t) := fun s hs => (hθ s hs).continuousWithinAt
  have hcont : ContinuousOn (fun s => θ s - (1 + Real.log δ) * s) (Set.Icc 0 t) :=
    hθcont.sub (ContinuousOn.mul continuousOn_const continuousOn_id)
  have hderiv : ∀ x ∈ interior (Set.Icc 0 t),
      HasDerivWithinAt (fun s => θ s - (1 + Real.log δ) * s)
        (fkField δ (θ x) - (1 + Real.log δ) * 1) (interior (Set.Icc 0 t)) x := by
    intro s hs
    have hsmem : s ∈ Set.Icc 0 t := interior_subset hs
    have h1 := (hθ s hsmem).mono interior_subset
    have h2 : HasDerivWithinAt (fun s => (1 + Real.log δ) * s) ((1 + Real.log δ) * 1)
        (interior (Set.Icc 0 t)) s :=
      HasDerivWithinAt.const_mul (1 + Real.log δ) (hasDerivWithinAt_id s _)
    exact h1.sub h2
  have hnonneg : ∀ x ∈ interior (Set.Icc 0 t),
      0 ≤ fkField δ (θ x) - (1 + Real.log δ) * 1 := by
    intro s hs
    have h := one_add_log_le_fkField hδ (θ s)
    linarith
  have hmono : MonotoneOn (fun s => θ s - (1 + Real.log δ) * s) (Set.Icc 0 t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hcont hderiv hnonneg
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht
  have htmem : t ∈ Set.Icc 0 t := Set.right_mem_Icc.mpr ht
  have hle := hmono h0 htmem ht
  change θ 0 - (1 + Real.log δ) * 0 ≤ θ t - (1 + Real.log δ) * t at hle
  rw [mul_zero, sub_zero] at hle
  linarith

/-- Time-in-box bound: for `δ > exp (-1)`, a solution on `[0, t]` that stays at or below `b`
has `t ≤ (b - θ 0) / (1 + log δ)`. -/
lemma fk_time_le_of_le {δ b t : ℝ} (hδ : Real.exp (-1) < δ) (ht : 0 ≤ t) {θ : ℝ → ℝ}
    (hθ : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt θ (fkField δ (θ s)) (Set.Icc 0 t) s)
    (hb : ∀ s ∈ Set.Icc 0 t, θ s ≤ b) :
    t ≤ (b - θ 0) / (1 + Real.log δ) := by
  have hδpos : 0 < δ := lt_trans (Real.exp_pos _) hδ
  have hc : 0 < 1 + Real.log δ := (one_add_log_pos_iff hδpos).mpr hδ
  have hlb := fk_solution_lower_bound hδpos ht hθ
  have hbt : θ t ≤ b := hb t (Set.right_mem_Icc.mpr ht)
  rw [le_div_iff₀ hc]
  linarith

/-- Stopped exit from a declared validity box `[a, b]`, `a ≤ θ₀ < b`, for `δ > exp (-1)`: some
solution starting at `θ₀` stays in the box on `[0, τ]` and reaches the top `b` at a time
`0 < τ ≤ (b - θ₀) / (1 + log δ)`. -/
lemma fk_exists_box_exit {δ a b θ₀ : ℝ} (hδ : Real.exp (-1) < δ) (ha : a ≤ θ₀)
    (hb : θ₀ < b) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ (b - θ₀) / (1 + Real.log δ) ∧
      ∃ θ : ℝ → ℝ, θ 0 = θ₀ ∧ θ τ = b ∧ (∀ s ∈ Set.Icc 0 τ, θ s ∈ Set.Icc a b) ∧
        ∀ s ∈ Set.Icc 0 τ, HasDerivWithinAt θ (fkField δ (θ s)) (Set.Icc 0 τ) s := by
  have hδpos : 0 < δ := lt_trans (Real.exp_pos _) hδ
  have hc : 0 < 1 + Real.log δ := (one_add_log_pos_iff hδpos).mpr hδ
  have hab : a < b := lt_of_le_of_lt ha hb
  set c := 1 + Real.log δ with hcdef
  set Tstar := (b - θ₀) / c with hTdef
  have hTnn : 0 ≤ Tstar := by
    rw [hTdef]
    exact le_of_lt (div_pos (sub_pos.mpr hb) hc)
  set L0 := |δ * Real.exp a - 1| + |δ * Real.exp b - 1| + 1 with hL0def
  have hL0nn : 0 ≤ L0 := by
    rw [hL0def]
    positivity
  have hL0bound : ∀ w ∈ Set.Icc a b, |δ * Real.exp w - 1| ≤ L0 := by
    intro w hw
    have he1 : δ * Real.exp a ≤ δ * Real.exp w :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw.1) (le_of_lt hδpos)
    have he2 : δ * Real.exp w ≤ δ * Real.exp b :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw.2) (le_of_lt hδpos)
    rw [hL0def, abs_le]
    constructor
    · have h1 : δ * Real.exp a - 1 ≤ δ * Real.exp w - 1 := by linarith
      have h2 := neg_abs_le (δ * Real.exp a - 1)
      have hnn : (0 : ℝ) ≤ |δ * Real.exp b - 1| + 1 := by positivity
      linarith
    · have h1 : δ * Real.exp w - 1 ≤ δ * Real.exp b - 1 := by linarith
      have h2 := le_abs_self (δ * Real.exp b - 1)
      have hnn : (0 : ℝ) ≤ |δ * Real.exp a - 1| + 1 := by positivity
      linarith
  have hgderiv : ∀ x : ℝ, HasDerivAt (fkField δ) (δ * Real.exp x - 1) x := by
    intro x
    exact HasDerivAt.sub
      (HasDerivAt.const_mul δ (Real.hasDerivAt_exp x)) (hasDerivAt_id x)
  have hgcont : ∀ p q : ℝ, ContinuousOn (fkField δ) (Set.Icc p q) := by
    intro p q
    change ContinuousOn (fun u => δ * Real.exp u - u) (Set.Icc p q)
    exact ((continuous_const.mul Real.continuous_exp).sub continuous_id).continuousOn
  have hgdiff : ∀ p q : ℝ, DifferentiableOn ℝ (fkField δ) (Set.Ioo p q) := by
    intro p q x _
    exact (hgderiv x).differentiableAt.differentiableWithinAt
  have hAlt : ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u < v →
      |fkField δ u - fkField δ v| ≤ L0 * |u - v| := by
    intro u v hu hv huv
    obtain ⟨w, hwmem, hweq⟩ := exists_deriv_eq_slope (fkField δ) huv (hgcont u v) (hgdiff u v)
    have hwbox : w ∈ Set.Icc a b :=
      ⟨le_trans hu.1 (le_of_lt hwmem.1), le_trans (le_of_lt hwmem.2) hv.2⟩
    have hder : deriv (fkField δ) w = δ * Real.exp w - 1 := (hgderiv w).deriv
    have hbound : |δ * Real.exp w - 1| ≤ L0 := hL0bound w hwbox
    have hpos : 0 < v - u := sub_pos.mpr huv
    have hne : v - u ≠ 0 := ne_of_gt hpos
    have e : fkField δ v - fkField δ u = (δ * Real.exp w - 1) * (v - u) := by
      rw [hder] at hweq
      exact ((eq_div_iff_mul_eq hne).mp hweq).symm
    have e2 : fkField δ u - fkField δ v = -((δ * Real.exp w - 1) * (v - u)) := by
      linarith [e]
    rw [e2, abs_neg, abs_mul]
    have e3 : |v - u| = |u - v| := abs_sub_comm v u
    rw [e3]
    exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
  have hA : ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b →
      |fkField δ u - fkField δ v| ≤ L0 * |u - v| := by
    intro u v hu hv
    rcases lt_trichotomy u v with h | h | h
    · exact hAlt u v hu hv h
    · subst h
      simp
    · have h2 := hAlt v u hv hu h
      rw [abs_sub_comm (fkField δ u) (fkField δ v), abs_sub_comm u v]
      exact h2
  have hC : ∀ x : ℝ, max a (min x b) ∈ Set.Icc a b := by
    intro x
    constructor
    · exact le_max_left _ _
    · exact max_le_iff.mpr ⟨le_of_lt hab, min_le_right _ _⟩
  have hBle : ∀ x y : ℝ, x ≤ y → |max a (min x b) - max a (min y b)| ≤ |x - y| := by
    intro x y hxy
    rcases le_total y a with hya | hya
    · have hx : x ≤ a := le_trans hxy hya
      have hxb : min x b = x := min_eq_left (le_trans hx (le_of_lt hab))
      have hyb : min y b = y := min_eq_left (le_trans hya (le_of_lt hab))
      rw [hxb, hyb, max_eq_left hx, max_eq_left hya, sub_self, abs_zero]
      exact abs_nonneg _
    · rcases le_total b x with hbx | hbx
      · have hy : b ≤ y := le_trans hbx hxy
        have hxb : min x b = b := min_eq_right hbx
        have hyb : min y b = b := min_eq_right hy
        rw [hxb, hyb, max_eq_right (le_of_lt hab), sub_self, abs_zero]
        exact abs_nonneg _
      · rcases le_total x a with hxa | hxa <;> rcases le_total y b with hyb | hyb
        · have hxb : min x b = x := min_eq_left (le_of_lt (lt_of_le_of_lt hxa hab))
          have hyb' : min y b = y := min_eq_left hyb
          rw [hxb, hyb', max_eq_left hxa, max_eq_right hya,
            abs_of_nonpos (sub_nonpos.mpr hya), abs_of_nonpos (sub_nonpos.mpr hxy)]
          linarith
        · have hxb : min x b = x := min_eq_left (le_of_lt (lt_of_le_of_lt hxa hab))
          have hyb' : min y b = b := min_eq_right hyb
          rw [hxb, hyb', max_eq_left hxa, max_eq_right (le_of_lt hab),
            abs_of_nonpos (sub_nonpos.mpr (le_of_lt hab)),
            abs_of_nonpos (sub_nonpos.mpr hxy)]
          linarith
        · have hxb : min x b = x := min_eq_left hbx
          have hyb' : min y b = y := min_eq_left hyb
          rw [hxb, hyb', max_eq_right hxa, max_eq_right (le_trans hxa hxy)]
        · have hxb : min x b = x := min_eq_left hbx
          have hyb' : min y b = b := min_eq_right hyb
          rw [hxb, hyb', max_eq_right hxa, max_eq_right (le_of_lt hab),
            abs_of_nonpos (sub_nonpos.mpr hbx), abs_of_nonpos (sub_nonpos.mpr hxy)]
          linarith
  have hB : ∀ x y : ℝ, |max a (min x b) - max a (min y b)| ≤ |x - y| := by
    intro x y
    rcases le_total x y with hxy | hxy
    · exact hBle x y hxy
    · have h := hBle y x hxy
      rw [abs_sub_comm x y]
      rwa [abs_sub_comm (max a (min x b)) (max a (min y b))]
  have hLip : LipschitzWith ⟨L0, hL0nn⟩ (fun u : ℝ => fkField δ (max a (min u b))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq]
    calc |fkField δ (max a (min x b)) - fkField δ (max a (min y b))|
        ≤ L0 * |max a (min x b) - max a (min y b)| := hA _ _ (hC x) (hC y)
      _ ≤ L0 * |x - y| := mul_le_mul_of_nonneg_left (hB x y) hL0nn
  set M := δ * Real.exp b + |a| + |b| + 1 with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    positivity
  have hMbound : ∀ w ∈ Set.Icc a b, |fkField δ w| ≤ M := by
    intro w hw
    have he : Real.exp w ≤ Real.exp b := Real.exp_le_exp.mpr hw.2
    have hA1 : δ * Real.exp w ≤ δ * Real.exp b :=
      mul_le_mul_of_nonneg_left he (le_of_lt hδpos)
    have hW : |w| ≤ |a| + |b| := by
      rw [abs_le]
      constructor
      · calc -(|a| + |b|) ≤ -|a| := by
              apply neg_le_neg
              exact le_add_of_nonneg_right (abs_nonneg b)
          _ ≤ a := neg_abs_le a
          _ ≤ w := hw.1
      · calc w ≤ b := hw.2
          _ ≤ |b| := le_abs_self b
          _ ≤ |a| + |b| := le_add_of_nonneg_left (abs_nonneg a)
    change |δ * Real.exp w - w| ≤ M
    rw [hMdef]
    calc |δ * Real.exp w - w| ≤ |δ * Real.exp w| + |w| := abs_sub _ _
      _ = δ * Real.exp w + |w| := by
        rw [abs_of_nonneg (mul_nonneg (le_of_lt hδpos) (Real.exp_pos _).le)]
      _ ≤ δ * Real.exp b + (|a| + |b|) := add_le_add hA1 hW
      _ ≤ δ * Real.exp b + |a| + |b| + 1 := by
        have h01 : (0 : ℝ) ≤ 1 := zero_le_one
        linarith
  have hPL : IsPicardLindelof (fun _ u : ℝ => fkField δ (max a (min u b)))
      (⟨0, Set.left_mem_Icc.mpr hTnn⟩ : ↥(Set.Icc 0 Tstar)) θ₀
      ⟨M * Tstar + 1, by positivity⟩ 0 ⟨M, hMnn⟩ ⟨L0, hL0nn⟩ := {
    lipschitzOnWith := by
      intro t ht
      exact hLip.lipschitzOnWith
    continuousOn := by
      intro x hx
      change ContinuousOn (fun _ : ℝ => fkField δ (max a (min x b))) (Set.Icc 0 Tstar)
      exact continuousOn_const
    norm_le := by
      intro t ht x hx
      change ‖fkField δ (max a (min x b))‖ ≤ M
      rw [Real.norm_eq_abs]
      exact hMbound _ (hC x)
    mul_max_le := by
      change M * max (Tstar - 0) (0 - 0) ≤ (M * Tstar + 1) - 0
      have hmax : max (Tstar - 0) (0 - 0) = Tstar := by
        rw [sub_zero, sub_zero]
        exact max_eq_left hTnn
      rw [hmax, sub_zero]
      exact le_add_of_nonneg_right zero_le_one
  }
  obtain ⟨θ, hθ0, hθode⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hPL
  have hθ0' : θ 0 = θ₀ := hθ0
  have hθcont : ContinuousOn θ (Set.Icc 0 Tstar) :=
    fun s hs => (hθode s hs).continuousWithinAt
  have hcont : ContinuousOn (fun s => θ s - c * s) (Set.Icc 0 Tstar) :=
    hθcont.sub (ContinuousOn.mul continuousOn_const continuousOn_id)
  have hderiv : ∀ x ∈ interior (Set.Icc 0 Tstar),
      HasDerivWithinAt (fun s => θ s - c * s)
        (fkField δ (max a (min (θ x) b)) - c * 1) (interior (Set.Icc 0 Tstar)) x := by
    intro s hs
    have hsmem : s ∈ Set.Icc 0 Tstar := interior_subset hs
    have h1 : HasDerivWithinAt θ (fkField δ (max a (min (θ s) b)))
        (interior (Set.Icc 0 Tstar)) s :=
      (hθode s hsmem).mono interior_subset
    have h2 : HasDerivWithinAt (fun s => c * s) (c * 1)
        (interior (Set.Icc 0 Tstar)) s :=
      HasDerivWithinAt.const_mul c (hasDerivWithinAt_id s _)
    exact h1.sub h2
  have hnonneg : ∀ x ∈ interior (Set.Icc 0 Tstar),
      0 ≤ fkField δ (max a (min (θ x) b)) - c * 1 := by
    intro s hs
    have h := one_add_log_le_fkField hδpos (max a (min (θ s) b))
    rw [hcdef]
    linarith
  have hmono : MonotoneOn (fun s => θ s - c * s) (Set.Icc 0 Tstar) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Tstar) hcont hderiv hnonneg
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 Tstar := Set.left_mem_Icc.mpr hTnn
  have hgrow : ∀ s ∈ Set.Icc 0 Tstar, θ 0 + c * s ≤ θ s := by
    intro s hs
    have h := hmono h0_mem hs hs.1
    change θ 0 - c * 0 ≤ θ s - c * s at h
    rw [mul_zero, sub_zero] at h
    linarith
  have hTstar_mem : Tstar ∈ Set.Icc 0 Tstar := Set.right_mem_Icc.mpr hTnn
  have hcT : c * Tstar = b - θ₀ := by
    have hcne : c ≠ 0 := ne_of_gt hc
    rw [hTdef]
    field_simp
  have hb_le : b ≤ θ Tstar := by
    have h := hgrow Tstar hTstar_mem
    rw [hθ0', hcT] at h
    linarith
  have hIVT := intermediate_value_Icc hTnn hθcont
  have hbmem : b ∈ Set.Icc (θ 0) (θ Tstar) := by
    rw [hθ0']
    exact ⟨hb.le, hb_le⟩
  obtain ⟨τ, hτmem, hτeq⟩ := hIVT hbmem
  have hτpos : 0 < τ := by
    rcases eq_or_lt_of_le hτmem.1 with h0eq | h0lt
    · subst h0eq
      rw [hθ0'] at hτeq
      linarith
    · exact h0lt
  have hbox : ∀ s ∈ Set.Icc 0 τ, θ s ∈ Set.Icc a b := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 Tstar := ⟨hs.1, le_trans hs.2 hτmem.2⟩
    constructor
    · have h := hgrow s hsT
      rw [hθ0'] at h
      have hcs : 0 ≤ c * s := mul_nonneg (le_of_lt hc) hs.1
      linarith
    · have h := hmono hsT hτmem hs.2
      change θ s - c * s ≤ θ τ - c * τ at h
      rw [hτeq] at h
      have hexpand : c * (τ - s) = c * τ - c * s := by ring
      have hcs : 0 ≤ c * (τ - s) := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hs.2)
      rw [hexpand] at hcs
      linarith
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 Tstar := fun s hs => ⟨hs.1, le_trans hs.2 hτmem.2⟩
  have hode : ∀ s ∈ Set.Icc 0 τ, HasDerivWithinAt θ (fkField δ (θ s)) (Set.Icc 0 τ) s := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 Tstar := hsub hs
    have h1 := hθode s hsT
    have hboxs := hbox s hs
    have h2 : fkField δ (max a (min (θ s) b)) = fkField δ (θ s) := by
      rw [min_eq_left hboxs.2, max_eq_right hboxs.1]
    rw [h2] at h1
    exact h1.mono hsub
  have hτle : τ ≤ (b - θ₀) / c := by
    have h := fk_time_le_of_le (t := τ) hδ (le_of_lt hτpos) hode
      (fun s hs => (hbox s hs).2)
    rw [hθ0'] at h
    rwa [hcdef]
  exact ⟨τ, hτpos, hτle, θ, hθ0', hτeq, hbox, hode⟩

end Chemistry.CombustionAcoustics
