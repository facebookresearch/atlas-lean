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
claimed unique), and every actual forward solution starting from
positive data is trapped between `min (T 0) Ta` and
`max (T 0) (Ta + G / H)`, so this exact model has no unbounded
temperature runaway. Constant reactant and cooling coefficients are
model inputs; no empirical adequacy is claimed.

## ii. Key results

- `CombustionAcoustics.arrhenius_equilibrium_exists`: an equilibrium
  temperature exists in the stated bracket.
- `CombustionAcoustics.arrhenius_solution_trapped`: forward
  solutions are trapped in the stated interval.

## iii. Table of contents

- A. Arrhenius equilibrium and trapping

## iv. References

- The sign bracket is the classical Semenov/Frank-Kamenetskii
  zeroth-order balance; the formal statement is self-contained.

## A. Arrhenius equilibrium and trapping

-/

@[expose] public section

namespace CombustionAcoustics

/-- Zeroth-order Arrhenius heat-release rate with Newton cooling:
`rate(T) = G * exp(-B / T) - H * (T - Ta)`, for heat-generation scale
`G`, cooling coefficient `H`, activation ratio `B = E / R`, and
ambient `Ta`. Read for `T > 0`. -/
noncomputable def arrheniusRate (G H B Ta T : ℝ) : ℝ :=
  G * Real.exp (-B / T) - H * (T - Ta)

private lemma arrheniusRate_pos_of_le_ambient_all {G H B Ta T : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hle : T ≤ Ta) :
    0 < arrheniusRate G H B Ta T := by
  unfold arrheniusRate
  have hgen : 0 < G * Real.exp (-B / T) := mul_pos hG (Real.exp_pos _)
  have hcool : H * (T - Ta) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hH) (sub_nonpos.mpr hle)
  linarith

private lemma arrheniusRate_neg_of_gt_upper {G H B Ta T : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) (hlt : Ta + G / H < T) :
    arrheniusRate G H B Ta T < 0 := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hGH : 0 < G / H := div_pos hG hH
  have hTpos : 0 < T := by
    have hpos : (0:ℝ) < Ta + G / H := by linarith
    exact lt_of_lt_of_le hpos (le_of_lt hlt)
  have hexp : Real.exp (-B / T) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hB) hTpos
  have hgen : G * Real.exp (-B / T) < G := by
    calc G * Real.exp (-B / T) < G * 1 := mul_lt_mul_of_pos_left hexp hG
      _ = G := mul_one G
  have hcool : G < H * (T - Ta) := by
    have h1 : G / H < T - Ta := by linarith
    have h2 : H * (G / H) < H * (T - Ta) := mul_lt_mul_of_pos_left h1 hH
    have h3 : H * (G / H) = G := by
      rw [mul_comm H (G / H)]
      exact div_mul_cancel₀ G hHne
    linarith
  unfold arrheniusRate
  linarith

private lemma exists_right_of {s t : ℝ} (hlt : s < t) {P : ℝ → Prop}
    (hev : ∀ᶠ u in nhds s, P u) : ∃ u ∈ Set.Ioo s t, P u := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set δ : ℝ := min ε (t - s) / 2 with hδdef
  have hmin_pos : 0 < min ε (t - s) := lt_min hεpos (by linarith)
  have hδpos : 0 < δ := by linarith
  have hδ_lt_ε : δ < ε := by
    have h1 : min ε (t - s) ≤ ε := min_le_left _ _
    linarith
  have hδ_lt_ts : δ < t - s := by
    have h1 : min ε (t - s) ≤ t - s := min_le_right _ _
    linarith
  refine ⟨s + δ, ⟨by linarith, by linarith⟩, ?_⟩
  apply hε
  rw [Metric.mem_ball, Real.dist_eq]
  have hsub : s + δ - s = δ := by ring
  rw [hsub, abs_of_pos hδpos]
  exact hδ_lt_ε

private lemma barrier_upper {T : ℝ → ℝ} {hi t : ℝ} (hcont : Continuous T) (ht : 0 ≤ t)
    (hT0 : T 0 ≤ hi)
    (hderiv : ∀ c : ℝ, hi ≤ T c → deriv T c < 0) :
    T t ≤ hi := by
  by_contra hcon
  push Not at hcon
  have h0mem : (0:ℝ) ∈ {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} :=
    ⟨Set.mem_Icc.mpr ⟨le_refl 0, ht⟩, hT0⟩
  have hAbdd : BddAbove {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} :=
    ⟨t, fun u hu => (Set.mem_Icc.mp hu.1).2⟩
  have hAne : {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi}.Nonempty := ⟨0, h0mem⟩
  have hAclosed : IsClosed {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} := by
    have heq : {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} = Set.Icc (0:ℝ) t ∩ T ⁻¹' (Set.Iic hi) := by
      ext u
      simp
    rw [heq]
    exact isClosed_Icc.inter (isClosed_Iic.preimage hcont)
  set s : ℝ := sSup {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} with hsdef
  have hsA : s ∈ {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} := by
    rw [hsdef]
    exact hAclosed.csSup_mem hAne hAbdd
  have hsIcc : s ∈ Set.Icc (0:ℝ) t := hsA.1
  have hs_le : s ≤ t := (Set.mem_Icc.mp hsIcc).2
  have hs_ge : 0 ≤ s := (Set.mem_Icc.mp hsIcc).1
  have hTs_le : T s ≤ hi := hsA.2
  have hs_lt : s < t := by
    by_contra hle
    push Not at hle
    have hst : s = t := le_antisymm hs_le hle
    rw [hst] at hTs_le
    linarith
  have hTs_eq : T s = hi := by
    by_contra hne
    have hlt : T s < hi := lt_of_le_of_ne hTs_le hne
    have htend : Filter.Tendsto T (nhds s) (nhds (T s)) := hcont.continuousAt
    have hev : ∀ᶠ u in nhds s, T u < hi := by
      have h1 : ∀ᶠ y in nhds (T s), y ∈ Set.Iio hi := isOpen_Iio.eventually_mem hlt
      have h2 : ∀ᶠ y in nhds (T s), y < hi := h1
      exact htend.eventually h2
    obtain ⟨u, huIoo, huP⟩ := exists_right_of hs_lt hev
    have huIoo' := Set.mem_Ioo.mp huIoo
    have huIcc : u ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr
      ⟨le_trans hs_ge (le_of_lt huIoo'.1), le_of_lt huIoo'.2⟩
    have huA : u ∈ {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} := ⟨huIcc, le_of_lt huP⟩
    have h := le_csSup hAbdd huA
    rw [← hsdef] at h
    linarith [huIoo'.1]
  have hle_s : hi ≤ T s := le_of_eq hTs_eq.symm
  have hds_neg : deriv T s < 0 := hderiv s hle_s
  have hdiff_s : DifferentiableAt ℝ T s := differentiableAt_of_deriv_ne_zero (ne_of_lt hds_neg)
  have hder : HasDerivAt T (deriv T s) s := hdiff_s.hasDerivAt
  have ho := HasDerivAt.isLittleO hder
  have hcpos : 0 < -(deriv T s) / 2 := by linarith
  have hev0 : ∀ᶠ u in nhds s, ‖T u - T s - (u - s) • (deriv T s)‖ ≤ (-(deriv T s) / 2) * ‖u - s‖ :=
    (Asymptotics.isLittleO_iff.mp ho) hcpos
  obtain ⟨u, huIoo, huP⟩ := exists_right_of hs_lt hev0
  have huIoo' := Set.mem_Ioo.mp huIoo
  have hus_pos : 0 < u - s := by linarith [huIoo'.1]
  rw [smul_eq_mul] at huP
  simp only [Real.norm_eq_abs] at huP
  rw [abs_of_pos hus_pos] at huP
  have hle : T u - T s - (u - s) * deriv T s ≤ (-(deriv T s) / 2) * (u - s) :=
    le_trans (le_abs_self _) huP
  have hneg2 : (u - s) * (deriv T s / 2) < 0 :=
    mul_neg_of_pos_of_neg hus_pos (by linarith)
  have hfin : T u - T s < 0 := by
    have hdecomp : T u - T s = (T u - T s - (u - s) * deriv T s) + (u - s) * deriv T s := by ring
    have hid : (-(deriv T s) / 2) * (u - s) + (u - s) * deriv T s = (u - s) * (deriv T s / 2) := by ring
    linarith
  rw [hTs_eq] at hfin
  have huIcc : u ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr
    ⟨le_trans hs_ge (le_of_lt huIoo'.1), le_of_lt huIoo'.2⟩
  have hu_not : u ∉ {u ∈ Set.Icc (0:ℝ) t | T u ≤ hi} := by
    intro huA
    have h := le_csSup hAbdd huA
    rw [← hsdef] at h
    linarith [huIoo'.1]
  have hTgt : hi < T u := by
    by_contra hle2
    push Not at hle2
    exact hu_not ⟨huIcc, hle2⟩
  linarith

private lemma barrier_lower {T : ℝ → ℝ} {lo t : ℝ} (hcont : Continuous T) (ht : 0 ≤ t)
    (hT0 : lo ≤ T 0)
    (hderiv : ∀ c : ℝ, T c ≤ lo → 0 < deriv T c) :
    lo ≤ T t := by
  by_contra hcon
  push Not at hcon
  have h0mem : (0:ℝ) ∈ {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} :=
    ⟨Set.mem_Icc.mpr ⟨le_refl 0, ht⟩, hT0⟩
  have hAbdd : BddAbove {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} :=
    ⟨t, fun u hu => (Set.mem_Icc.mp hu.1).2⟩
  have hAne : {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u}.Nonempty := ⟨0, h0mem⟩
  have hAclosed : IsClosed {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} := by
    have heq : {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} = Set.Icc (0:ℝ) t ∩ T ⁻¹' (Set.Ici lo) := by
      ext u
      simp
    rw [heq]
    exact isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  set s : ℝ := sSup {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} with hsdef
  have hsA : s ∈ {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} := by
    rw [hsdef]
    exact hAclosed.csSup_mem hAne hAbdd
  have hsIcc : s ∈ Set.Icc (0:ℝ) t := hsA.1
  have hs_le : s ≤ t := (Set.mem_Icc.mp hsIcc).2
  have hs_ge : 0 ≤ s := (Set.mem_Icc.mp hsIcc).1
  have hTs_ge : lo ≤ T s := hsA.2
  have hs_lt : s < t := by
    by_contra hle
    push Not at hle
    have hst : s = t := le_antisymm hs_le hle
    rw [hst] at hTs_ge
    linarith
  have hTs_eq : T s = lo := by
    by_contra hne
    have hne' : lo ≠ T s := Ne.symm hne
    have hlt : lo < T s := lt_of_le_of_ne hTs_ge hne'
    have htend : Filter.Tendsto T (nhds s) (nhds (T s)) := hcont.continuousAt
    have hev : ∀ᶠ u in nhds s, lo < T u := by
      have h1 : ∀ᶠ y in nhds (T s), y ∈ Set.Ioi lo := isOpen_Ioi.eventually_mem hlt
      have h2 : ∀ᶠ y in nhds (T s), lo < y := h1
      exact htend.eventually h2
    obtain ⟨u, huIoo, huP⟩ := exists_right_of hs_lt hev
    have huIoo' := Set.mem_Ioo.mp huIoo
    have huIcc : u ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr
      ⟨le_trans hs_ge (le_of_lt huIoo'.1), le_of_lt huIoo'.2⟩
    have huA : u ∈ {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} := ⟨huIcc, le_of_lt huP⟩
    have h := le_csSup hAbdd huA
    rw [← hsdef] at h
    linarith [huIoo'.1]
  have hle_s : T s ≤ lo := le_of_eq hTs_eq
  have hds_pos : 0 < deriv T s := hderiv s hle_s
  have hdiff_s : DifferentiableAt ℝ T s := differentiableAt_of_deriv_ne_zero (ne_of_gt hds_pos)
  have hder : HasDerivAt T (deriv T s) s := hdiff_s.hasDerivAt
  have ho := HasDerivAt.isLittleO hder
  have hcpos : 0 < deriv T s / 2 := by linarith
  have hev0 : ∀ᶠ u in nhds s, ‖T u - T s - (u - s) • (deriv T s)‖ ≤ (deriv T s / 2) * ‖u - s‖ :=
    (Asymptotics.isLittleO_iff.mp ho) hcpos
  obtain ⟨u, huIoo, huP⟩ := exists_right_of hs_lt hev0
  have huIoo' := Set.mem_Ioo.mp huIoo
  have hus_pos : 0 < u - s := by linarith [huIoo'.1]
  rw [smul_eq_mul] at huP
  simp only [Real.norm_eq_abs] at huP
  rw [abs_of_pos hus_pos] at huP
  have hpos2 : 0 < (u - s) * (deriv T s / 2) := mul_pos hus_pos (by linarith)
  have hfin : 0 < T u - T s := by
    have hdecomp : T u - T s = (T u - T s - (u - s) * deriv T s) + (u - s) * deriv T s := by ring
    have hlow : -((deriv T s / 2) * (u - s)) ≤ T u - T s - (u - s) * deriv T s := by
      have h2 := neg_abs_le (T u - T s - (u - s) * deriv T s)
      linarith [huP]
    have hid : -((deriv T s / 2) * (u - s)) + (u - s) * deriv T s = (u - s) * (deriv T s / 2) := by ring
    linarith
  rw [hTs_eq] at hfin
  have huIcc : u ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr
    ⟨le_trans hs_ge (le_of_lt huIoo'.1), le_of_lt huIoo'.2⟩
  have hu_not : u ∉ {u ∈ Set.Icc (0:ℝ) t | lo ≤ T u} := by
    intro huA
    have h := le_csSup hAbdd huA
    rw [← hsdef] at h
    linarith [huIoo'.1]
  have hTlt : T u < lo := by
    by_contra hle2
    push Not at hle2
    exact hu_not ⟨huIcc, hle2⟩
  linarith

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
  have _hT : 0 < T := hT
  exact arrheniusRate_pos_of_le_ambient_all hG hH hle

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
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hB) hTpos
  have hgen : G * Real.exp (-B / (Ta + G / H)) < G := by
    calc G * Real.exp (-B / (Ta + G / H)) < G * 1 := mul_lt_mul_of_pos_left hexp hG
      _ = G := mul_one G
  have hcool : H * (Ta + G / H - Ta) = G := by
    have e : Ta + G / H - Ta = G / H := by ring
    rw [e, mul_comm H (G / H)]
    exact div_mul_cancel₀ G hHne
  unfold arrheniusRate
  linarith

/-- Equilibrium existence: for `G, H, B, Ta > 0` there is an
equilibrium temperature in the open interval `(Ta, Ta + G / H)`. No
uniqueness is claimed. -/
theorem arrhenius_equilibrium_exists {G H B Ta : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) :
    ∃ T : ℝ, T ∈ Set.Ioo Ta (Ta + G / H) ∧ arrheniusRate G H B Ta T = 0 := by
  have hGH : 0 < G / H := div_pos hG hH
  have hab : Ta ≤ Ta + G / H := by linarith
  have hpos : 0 < arrheniusRate G H B Ta Ta := arrheniusRate_pos_ambient hG
  have hneg : arrheniusRate G H B Ta (Ta + G / H) < 0 :=
    arrheniusRate_neg_at_upper hG hH hB hTa
  have hne : ∀ T ∈ Set.Icc Ta (Ta + G / H), T ≠ 0 := by
    intro T hT
    have hle : Ta ≤ T := (Set.mem_Icc.mp hT).1
    exact ne_of_gt (lt_of_lt_of_le hTa hle)
  have hdiv : ContinuousOn (fun T : ℝ => -B / T) (Set.Icc Ta (Ta + G / H)) :=
    continuousOn_const.div continuousOn_id hne
  have hexp : ContinuousOn (fun T : ℝ => Real.exp (-B / T)) (Set.Icc Ta (Ta + G / H)) :=
    Real.continuous_exp.comp_continuousOn hdiv
  have hgen : ContinuousOn (fun T : ℝ => G * Real.exp (-B / T)) (Set.Icc Ta (Ta + G / H)) :=
    continuousOn_const.mul hexp
  have hsub : ContinuousOn (fun T : ℝ => T - Ta) (Set.Icc Ta (Ta + G / H)) :=
    continuousOn_id.sub continuousOn_const
  have hcool : ContinuousOn (fun T : ℝ => H * (T - Ta)) (Set.Icc Ta (Ta + G / H)) :=
    continuousOn_const.mul hsub
  have hcont : ContinuousOn (fun T => arrheniusRate G H B Ta T) (Set.Icc Ta (Ta + G / H)) := by
    show ContinuousOn (fun T => G * Real.exp (-B / T) - H * (T - Ta)) (Set.Icc Ta (Ta + G / H))
    exact hgen.sub hcool
  have hmem : (0:ℝ) ∈ Set.Ioo (arrheniusRate G H B Ta (Ta + G / H))
      (arrheniusRate G H B Ta Ta) := ⟨hneg, hpos⟩
  have himg := intermediate_value_Ioo' hab hcont hmem
  obtain ⟨T, hTmem, hTeq⟩ := himg
  exact ⟨T, hTmem, hTeq⟩

/-- Forward trapping for an actual solution: if `T` solves
`deriv T t = arrheniusRate G H B Ta (T t) / C` at every time, with
`C > 0`, and `T 0` lies in `[lo, hi]` where
`lo = min (T 0) Ta` and `hi = max (T 0) (Ta + G / H)`, then
`T t ∈ [lo, hi]` for every `t ≥ 0`. In particular the exact model has
no unbounded temperature runaway from positive initial data. -/
theorem arrhenius_solution_trapped {G H B Ta C : ℝ} (hG : 0 < G)
    (hH : 0 < H) (hB : 0 < B) (hTa : 0 < Ta) (hC : 0 < C)
    {T : ℝ → ℝ} (hT : ∀ t : ℝ, deriv T t = arrheniusRate G H B Ta (T t) / C)
    (hcont : Continuous T) {t : ℝ} (ht : 0 ≤ t) :
    T t ∈ Set.Icc (min (T 0) Ta) (max (T 0) (Ta + G / H)) := by
  rw [Set.mem_Icc]
  constructor
  · exact barrier_lower hcont ht (min_le_left _ _) (fun c hc => by
      have hle : T c ≤ Ta := le_trans hc (min_le_right _ _)
      have hrate : 0 < arrheniusRate G H B Ta (T c) :=
        arrheniusRate_pos_of_le_ambient_all hG hH hle
      rw [hT c]
      exact div_pos hrate hC)
  · exact barrier_upper hcont ht (le_max_left _ _) (fun c hc => by
      have hle : Ta + G / H ≤ T c := le_trans (le_max_right _ _) hc
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hrate : arrheniusRate G H B Ta (T c) < 0 :=
          arrheniusRate_neg_of_gt_upper hG hH hB hTa hlt
        rw [hT c]
        exact div_neg_of_neg_of_pos hrate hC
      · have hrate := arrheniusRate_neg_at_upper hG hH hB hTa
        rw [hT c, ← heq]
        exact div_neg_of_neg_of_pos hrate hC)

end CombustionAcoustics
