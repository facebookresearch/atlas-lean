/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Lipschitz
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PhyslibExt.SpaceSystems.MissionLedger
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Space thermal-power ports: radiator box trapping and battery loss heat

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

A battery on a finite mission schedule is charged with the terminal
power `Pc ≥ 0` or discharged with the terminal power `Pd ≥ 0` on each
interval `k` of length `dt k`, never both (`Pc * Pd = 0`), with
charge and discharge efficiencies `ηc, ηd ∈ (0, 1]`. The electrical
port law is a supplied model input: the stored energy changes by
`dt k * (ηc Pc k - Pd k / ηd)` (`batteryFlow`), so it is a stock of
`MissionLedger` and every prefix of the schedule, start and end
included, is checked by `MissionLedger.PrefixFeasible`; a feasible
terminal stock does not repair a deficit in the middle of an
eclipse. The terminal power `Pc - Pd` is counted positive when
absorbed by the battery and the storage power `ηc Pc - Pd / ηd`
positive when the stored energy grows; the port balance
`Pc - Pd = (ηc Pc - Pd / ηd) + q` defines the dissipated heat
`q = (1 - ηc) Pc + (1 / ηd - 1) Pd` (`batteryLossHeat`), which is
nonnegative. For `ηc = ηd = 4/5`, charging at `100 W` stores `80 W`
and dissipates `20 W`, and discharging `16 W` draws `20 W` from
storage and dissipates `4 W`. The heat of interval `j` is added to
the environmental heat input of mode `j` of the eclipse-mode
gluing; being nonnegative, it keeps the lower inward sign of the
radiator box, while the upper sign has to be checked on the total
heat input. Energies are in joules, powers in watts and durations in
seconds (or watt-hours, watts and hours throughout); efficiencies
are dimensionless. No electrochemical model, efficiency dependence,
degradation, illumination model or qualification claim is made.

## ii. Key results

- `ThermalPowerPorts.clippedRadiatorRate_lipschitzWith`: the
  clipped rate is globally Lipschitz with constant
  `Krad * (4 * Tmax^3) / C`, in `LipschitzWith` form (the
  pointwise form is `clippedRadiatorRate_lipschitz`).
- `ThermalPowerPorts.radiator_solution_trapped`: forward solutions
  with `HasDerivWithinAt` on `Set.Ici 0` starting in the box stay
  in the box for all `t ≥ 0`.
- `ThermalPowerPorts.radiator_solution_exists_trapped`: for every
  initial temperature in the box, the clipped field's global
  solution (global existence for globally Lipschitz fields) stays
  in the box for `t ≥ 0` and there solves the original field.
- `ThermalPowerPorts.terminalPower_eq_storage_add_loss`: the battery
  port balance; `batteryLossHeat_nonneg`: the dissipated heat is
  nonnegative; `battery_port_of_complementary`: with
  complementarity, storage power and heat depend on the terminal
  power only.
- `ThermalPowerPorts.stock_batteryFlow_succ`,
  `ThermalPowerPorts.prefixFeasible_battery`: the stored energy on the
  mission ledger, bounded at every prefix of a feasible schedule.
- `ThermalPowerPorts.batteryLossHeat_lower_sign`,
  `ThermalPowerPorts.batteryHeat_glued`: the battery heat keeps the
  lower inward sign and enters the eclipse-mode gluing as a heat
  input.

## iii. Table of contents

- A. The clipped radiator field and box trapping
- B. Battery loss heat and the mission schedule
  - B.1. Port law and dissipated heat
  - B.2. Stored energy on the mission ledger
  - B.3. Battery heat in the eclipse-mode gluing

## iv. References

- The model is the standard lumped Stefan-Boltzmann radiator
  balance; the statement is self-contained.
- J. R. Wertz and W. J. Larson (eds.), *Space Mission Analysis and
  Design*, 3rd edition, power-subsystem chapter (battery charge and
  discharge efficiencies, eclipse energy balance).
- D. G. Gilmore (ed.), *Spacecraft Thermal Control Handbook*, Vol. I,
  2nd edition (battery dissipation as an internal heat load).
- D. Linden and T. B. Reddy (eds.), *Handbook of Batteries*, 4th
  edition (charge and discharge efficiency and heat generation).
- `PhyslibExt.SpaceSystems.MissionLedger`: the every-prefix stock
  check reused for the stored energy.

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

private lemma abs_clip_sub_clip_le (Tmin Tmax a b : ℝ) :
    |min (max a Tmin) Tmax - min (max b Tmin) Tmax| ≤ |a - b| := by
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
  rw [sub_self, abs_zero]
  exact max_le (abs_max_sub_max_le_abs _ _ _) (abs_nonneg _)

private lemma abs_pow4_sub_le (x y Tmin Tmax : ℝ) (hmin : 0 ≤ Tmin)
    (hx : x ∈ Set.Icc Tmin Tmax) (hy : y ∈ Set.Icc Tmin Tmax) :
    |x ^ 4 - y ^ 4| ≤ (4 * Tmax ^ 3) * |x - y| := by
  have hx0 : (0 : ℝ) ≤ x := le_trans hmin hx.1
  have hy0 : (0 : ℝ) ≤ y := le_trans hmin hy.1
  have hmax3 : max |x| |y| ^ 3 ≤ Tmax ^ 3 := by
    apply pow_le_pow_left₀ _ _ 3
    · exact le_max_of_le_left (abs_nonneg _)
    · rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
      exact max_le hx.2 hy.2
  calc |x ^ 4 - y ^ 4|
      ≤ |x - y| * 4 * max |x| |y| ^ 3 := abs_pow_sub_pow_le x y 4
    _ ≤ |x - y| * 4 * Tmax ^ 3 :=
        mul_le_mul_of_nonneg_left hmax3
          (mul_nonneg (abs_nonneg _) (by norm_num))
    _ = (4 * Tmax ^ 3) * |x - y| := by ring

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

/-- The clipped rate in Mathlib's bundled `LipschitzWith` form,
with constant `Krad * (4 * Tmax^3) / C`, for direct consumption
by ODE existence/uniqueness APIs. -/
lemma clippedRadiatorRate_lipschitzWith {C Krad Q Tmin Tmax : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax) :
    LipschitzWith ⟨Krad * (4 * Tmax ^ 3) / C, by
      have hT0 : (0 : ℝ) ≤ Tmax := le_trans hmin hmax
      have h3 : (0 : ℝ) ≤ Tmax ^ 3 := pow_nonneg hT0 3
      have h4 : (0 : ℝ) ≤ 4 * Tmax ^ 3 := by linarith
      exact div_nonneg (mul_nonneg (le_of_lt hK) h4) (le_of_lt hC)⟩
      (clippedRadiatorRate C Krad Q Tmin Tmax) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq, Real.dist_eq]
  exact clippedRadiatorRate_lipschitz hC hK hmin hmax a b

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
        (hcont s0 hs0mem).continuousAt (Ici_mem_nhds hs0pos)
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
    exact (hT x (le_of_lt hx)).hasDerivAt (Ici_mem_nhds hx)
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
    obtain ⟨c, hcIoo, hc_slope⟩ := exists_hasDerivAt_eq_slope T
      (fun x => radiatorRate C Krad Q (T x)) hs0lt (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hc_slope' : radiatorRate C Krad Q (T c) = (T t - T s0) / (t - s0) := hc_slope
    have hts0 : t - s0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs0lt)
    have hmul : radiatorRate C Krad Q (T c) * (t - s0) = T t - T s0 :=
      (eq_div_iff hts0).mp hc_slope'
    have hcEq : T t - T s0 = (t - s0) * radiatorRate C Krad Q (T c) := by
      rw [mul_comm]
      exact hmul.symm
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
        obtain ⟨c, hcIoo, hc_slope⟩ := exists_hasDerivAt_eq_slope T
          (fun x => radiatorRate C Krad Q (T x)) hvs1 (hcontOn s1 v hs1mem.1)
          (fun x hx => hderivAt x (lt_of_le_of_lt hs1mem.1 hx.1))
        have hc_slope' : radiatorRate C Krad Q (T c) = (T v - T s1) / (v - s1) :=
          hc_slope
        have hvs1ne : v - s1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hvs1)
        have hcmul : radiatorRate C Krad Q (T c) * (v - s1) = T v - T s1 :=
          (eq_div_iff hvs1ne).mp hc_slope'
        have hcEq : T v - T s1 = (v - s1) * radiatorRate C Krad Q (T c) := by
          rw [mul_comm]
          exact hcmul.symm
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
          obtain ⟨d, hdIoo, hd_slope⟩ := exists_hasDerivAt_eq_slope T
            (fun x => radiatorRate C Krad Q (T x)) hcv (hcontOn c v hc0)
            (fun x hx => hderivAt x (lt_of_le_of_lt hc0 hx.1))
          have hd_slope' : radiatorRate C Krad Q (T d) = (T v - T c) / (v - c) :=
            hd_slope
          have hvcne : v - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcv)
          have hdmul : radiatorRate C Krad Q (T d) * (v - c) = T v - T c :=
            (eq_div_iff hvcne).mp hd_slope'
          have hdEq : T v - T c = (v - c) * radiatorRate C Krad Q (T d) := by
            rw [mul_comm]
            exact hdmul.symm
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
        have hble : (v - s1) * (Krad * (T c) ^ 4 / C) ≤
            (v - s1) * (Krad * (-T v) ^ 4 / C) := by
          have hKK : Krad * (T c) ^ 4 / C ≤ Krad * (-T v) ^ 4 / C := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h4le (le_of_lt hK)) (le_of_lt (inv_pos.mpr hC))
          exact mul_le_mul_of_nonneg_left hKK (le_of_lt (sub_pos.mpr hvs1))
        have hvsK : 0 < (v - s1) * Krad := mul_pos (sub_pos.mpr hvs1) hK
        rw [div_le_iff₀ hvsK]
        have h1 : -T v ≤ (v - s1) * (Krad * (-T v) ^ 4 / C) := by linarith [hwEq, hble]
        have hrw : (v - s1) * (Krad * (-T v) ^ 4 / C) =
            ((v - s1) * Krad * (-T v) ^ 4) / C := by ring
        rw [hrw] at h1
        have h2 : (-T v) * C ≤ (v - s1) * Krad * (-T v) ^ 4 :=
          (le_div_iff₀ hC).mp h1
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
      have hδpos : 0 < δ :=
        lt_min (by linarith) (lt_min (by linarith [hs1lt]) (by linarith))
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
            (nhdsWithin s1 (Set.Ioi s1)) (nhds (radiatorRate C Krad Q (T s1))) := by
          have hTend := hasDerivWithinAt_iff_tendsto_slope.mp (hT s1 hs1mem.1)
          have hsub : Set.Ioi s1 ⊆ Set.Ici 0 \ {s1} := by
            intro y hy
            have hy_lt : s1 < y := Set.mem_Ioi.mp hy
            rw [Set.mem_sdiff]
            constructor
            · show (0 : ℝ) ≤ y
              exact le_trans hs1mem.1 (le_of_lt hy_lt)
            · simp [ne_of_gt hy_lt]
          have hTend2 := hTend.mono_left (nhdsWithin_mono s1 hsub)
          have hcongr : (slope T s1) =ᶠ[nhdsWithin s1 (Set.Ioi s1)]
              (fun y => (T y - T s1) / (y - s1)) := by
            filter_upwards with y
            rw [slope_def_field]
          exact Filter.Tendsto.congr' hcongr hTend2
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
      obtain ⟨c, hcIoo, hc_slope⟩ := exists_hasDerivAt_eq_slope T
        (fun x => radiatorRate C Krad Q (T x)) hs0lt (hcontOn s0 t hs0mem.1)
        (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
      have hc_slope' : radiatorRate C Krad Q (T c) = (T t - T s0) / (t - s0) := hc_slope
      have hts0 : t - s0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs0lt)
      have hmul : radiatorRate C Krad Q (T c) * (t - s0) = T t - T s0 :=
        (eq_div_iff hts0).mp hc_slope'
      have hcEq : T t - T s0 = (t - s0) * radiatorRate C Krad Q (T c) := by
        rw [mul_comm]
        exact hmul.symm
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
lemma clippedRadiator_solution_trapped {C Krad Q Tmin Tmax : ℝ}
    (hC : 0 < C) (hmax : Tmin ≤ Tmax)
    (hlo : 0 ≤ Q - Krad * Tmin ^ 4) (hhi : Q - Krad * Tmax ^ 4 ≤ 0)
    {T : ℝ → ℝ}
    (hT : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T s)) (Set.Ici 0) s)
    (h0 : T 0 ∈ Set.Icc Tmin Tmax) {t : ℝ} (ht : 0 ≤ t) :
    T t ∈ Set.Icc Tmin Tmax := by
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
    exact (hT x (le_of_lt hx)).hasDerivAt (Ici_mem_nhds hx)
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
    obtain ⟨c, hcIoo, hc_slope⟩ := exists_hasDerivAt_eq_slope T
      (fun x => clippedRadiatorRate C Krad Q Tmin Tmax (T x)) hs0lt
      (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hc_slope' : clippedRadiatorRate C Krad Q Tmin Tmax (T c) =
        (T t - T s0) / (t - s0) := hc_slope
    have hts0 : t - s0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs0lt)
    have hmul : clippedRadiatorRate C Krad Q Tmin Tmax (T c) * (t - s0) =
        T t - T s0 := (eq_div_iff hts0).mp hc_slope'
    have hcEq : T t - T s0 =
        (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) := by
      rw [mul_comm]
      exact hmul.symm
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
    obtain ⟨c, hcIoo, hc_slope⟩ := exists_hasDerivAt_eq_slope T
      (fun x => clippedRadiatorRate C Krad Q Tmin Tmax (T x)) hs0lt
      (hcontOn s0 t hs0mem.1)
      (fun x hx => hderivAt x (lt_of_le_of_lt hs0mem.1 hx.1))
    have hc_slope' : clippedRadiatorRate C Krad Q Tmin Tmax (T c) =
        (T t - T s0) / (t - s0) := hc_slope
    have hts0 : t - s0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs0lt)
    have hmul : clippedRadiatorRate C Krad Q Tmin Tmax (T c) * (t - s0) =
        T t - T s0 := (eq_div_iff hts0).mp hc_slope'
    have hcEq : T t - T s0 =
        (t - s0) * clippedRadiatorRate C Krad Q Tmin Tmax (T c) := by
      rw [mul_comm]
      exact hmul.symm
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
lemma radiator_solution_exists_trapped {C Krad Q Tmin Tmax T0 : ℝ}
    (hC : 0 < C) (hK : 0 < Krad) (hmin : 0 ≤ Tmin) (hmax : Tmin ≤ Tmax)
    (hlo : 0 ≤ Q - Krad * Tmin ^ 4) (hhi : Q - Krad * Tmax ^ 4 ≤ 0)
    (h0 : T0 ∈ Set.Icc Tmin Tmax) :
    ∃ T : ℝ → ℝ, T 0 = T0 ∧
      (∀ t : ℝ, HasDerivAt T (clippedRadiatorRate C Krad Q Tmin Tmax (T t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → T t ∈ Set.Icc Tmin Tmax ∧
        HasDerivAt T (radiatorRate C Krad Q (T t)) t) := by
  have hlip := clippedRadiatorRate_lipschitzWith hC hK hmin hmax
    (Q := Q)
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
    clippedRadiator_solution_trapped hC hmax hlo hhi hTwithin h0T ht
  have hderiv : HasDerivAt T (radiatorRate C Krad Q (T t)) t := by
    have h := hT t
    rw [clippedRadiatorRate_eq_of_mem hmem] at h
    exact h
  exact ⟨hmem, hderiv⟩

/-- Gluing across a finite eclipse partition: given switch times
`τ 0 < τ 1 < ... < τ m` (`StrictMono τ`), per-mode forcings
`Q j`, a temperature `T` continuous on every closed piece
`[τ j, τ (j+1)]` and solving the mode-`j` radiator ODE on every
open piece, `T` is continuous on the whole horizon
`[τ 0, τ m]`. No classical derivative at the switches is
claimed. -/
theorem glued_continuous {C Krad : ℝ} {m : ℕ} {τ : ℕ → ℝ}
    (hτ : StrictMono τ) {Q : ℕ → ℝ} {T : ℝ → ℝ}
    (hcont : ∀ j : ℕ, j < m →
      ContinuousOn T (Set.Icc (τ j) (τ (j + 1))))
    (hode : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
      HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t) :
    ContinuousOn T (Set.Icc (τ 0) (τ m)) := by
  revert hcont hode
  induction m with
  | zero =>
    intro _hcont _hode
    rw [Set.Icc_self]
    exact continuousOn_singleton T (τ 0)
  | succ m ih =>
    intro hcont hode
    have hcont' : ∀ j : ℕ, j < m →
        ContinuousOn T (Set.Icc (τ j) (τ (j + 1))) :=
      fun j hj => hcont j (Nat.lt_trans hj (Nat.lt_succ_self m))
    have hode' : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
        HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t :=
      fun j hj => hode j (Nat.lt_trans hj (Nat.lt_succ_self m))
    have ih' := ih hcont' hode'
    have hlast := hcont m (Nat.lt_succ_self m)
    have h01 : τ 0 ≤ τ m := hτ.monotone (Nat.zero_le m)
    have h12 : τ m ≤ τ (m + 1) := hτ.monotone (Nat.le_succ m)
    have hunion : Set.Icc (τ 0) (τ m) ∪ Set.Icc (τ m) (τ (m + 1)) =
        Set.Icc (τ 0) (τ (m + 1)) :=
      Set.Icc_union_Icc_eq_Icc h01 h12
    have h := ContinuousOn.union_of_isClosed ih' hlast isClosed_Icc isClosed_Icc
    rwa [hunion] at h

/-- Integral form on each piece: for `j < m` and
`t ∈ [τ j, τ (j+1)]`,
`T t - T (τ j) = ∫ s in τ j..t, radiatorRate C Krad (Q j) (T s)`,
the fundamental theorem of calculus applied to the piecewise
solution. -/
theorem glued_integral_on_piece {C Krad : ℝ} (hC : 0 < C) {m : ℕ}
    {τ : ℕ → ℝ} (hτ : StrictMono τ) {Q : ℕ → ℝ} {T : ℝ → ℝ}
    (hcont : ∀ j : ℕ, j < m →
      ContinuousOn T (Set.Icc (τ j) (τ (j + 1))))
    (hode : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
      HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t)
    {j : ℕ} (hj : j < m) {t : ℝ} (ht : t ∈ Set.Icc (τ j) (τ (j + 1))) :
    T t - T (τ j) =
      ∫ s in τ j..t, radiatorRate C Krad (Q j) (T s) := by
  have _ := hτ
  have _ : C ≠ 0 := ne_of_gt hC
  have hTpiece : ContinuousOn T (Set.Icc (τ j) (τ (j + 1))) := hcont j hj
  have hpow : ContinuousOn (fun s => (T s) ^ 4) (Set.Icc (τ j) (τ (j + 1))) :=
    hTpiece.pow 4
  have hKrad : ContinuousOn (fun _ => Krad) (Set.Icc (τ j) (τ (j + 1))) :=
    continuousOn_const
  have hmul : ContinuousOn (fun s => Krad * (T s) ^ 4) (Set.Icc (τ j) (τ (j + 1))) :=
    hKrad.mul hpow
  have hQ : ContinuousOn (fun _ => Q j) (Set.Icc (τ j) (τ (j + 1))) :=
    continuousOn_const
  have hsub : ContinuousOn (fun s => Q j - Krad * (T s) ^ 4) (Set.Icc (τ j) (τ (j + 1))) :=
    hQ.sub hmul
  have hdiv : ContinuousOn (fun s => (Q j - Krad * (T s) ^ 4) / C)
      (Set.Icc (τ j) (τ (j + 1))) :=
    hsub.div_const C
  have hdiv' : ContinuousOn (fun s => radiatorRate C Krad (Q j) (T s))
      (Set.Icc (τ j) (τ (j + 1))) := by
    simpa [radiatorRate] using hdiv
  have hle : τ j ≤ t := ht.1
  have hte : t ≤ τ (j + 1) := ht.2
  have hsub_set : Set.Icc (τ j) t ⊆ Set.Icc (τ j) (τ (j + 1)) :=
    Set.Icc_subset_Icc le_rfl hte
  have hTsmall : ContinuousOn T (Set.Icc (τ j) t) := hTpiece.mono hsub_set
  have hdiv_small : ContinuousOn (fun s => radiatorRate C Krad (Q j) (T s))
      (Set.Icc (τ j) t) :=
    hdiv'.mono hsub_set
  have hint : IntervalIntegrable (fun s => radiatorRate C Krad (Q j) (T s))
      MeasureTheory.volume (τ j) t :=
    ContinuousOn.intervalIntegrable_of_Icc hle hdiv_small
  have hderiv : ∀ s ∈ Set.Ioo (τ j) t,
      HasDerivAt T (radiatorRate C Krad (Q j) (T s)) s := by
    intro s hs
    have hs3 : s < τ (j + 1) := lt_of_lt_of_le hs.2 hte
    exact hode j hj s ⟨hs.1, hs3⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hTsmall hderiv hint
  exact hftc.symm

/-- Box trapping across the switches: if every mode satisfies
the inward endpoint signs and the initial temperature is in the
box, and if every single-mode piece solution starting in the box
stays in the box on its piece (the single-mode trapping
principle, supplied as data), then the glued solution stays in
the box on the whole horizon. -/
theorem glued_trapped {C Krad Tmin Tmax : ℝ} {m : ℕ} {τ : ℕ → ℝ}
    (hτ : StrictMono τ) {Q : ℕ → ℝ} {T : ℝ → ℝ}
    (hcont : ∀ j : ℕ, j < m →
      ContinuousOn T (Set.Icc (τ j) (τ (j + 1))))
    (hode : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
      HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t)
    (htrap : ∀ j : ℕ, j < m → T (τ j) ∈ Set.Icc Tmin Tmax →
      ∀ t : ℝ, t ∈ Set.Icc (τ j) (τ (j + 1)) → T t ∈ Set.Icc Tmin Tmax)
    (h0 : T (τ 0) ∈ Set.Icc Tmin Tmax)
    {t : ℝ} (ht : t ∈ Set.Icc (τ 0) (τ m)) :
    T t ∈ Set.Icc Tmin Tmax := by
  have aux : ∀ (m : ℕ),
      (∀ j : ℕ, j < m → ContinuousOn T (Set.Icc (τ j) (τ (j + 1)))) →
      (∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
        HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t) →
      (∀ j : ℕ, j < m → T (τ j) ∈ Set.Icc Tmin Tmax →
        ∀ t : ℝ, t ∈ Set.Icc (τ j) (τ (j + 1)) → T t ∈ Set.Icc Tmin Tmax) →
      T (τ 0) ∈ Set.Icc Tmin Tmax →
      ∀ t : ℝ, t ∈ Set.Icc (τ 0) (τ m) → T t ∈ Set.Icc Tmin Tmax := by
    intro m
    induction m with
    | zero =>
      intro _ _ _ h0 t ht
      have heq : t = τ 0 := le_antisymm ht.2 ht.1
      rw [heq]
      exact h0
    | succ m ih =>
      intro hcont hode htrap h0 t ht
      have hcont' : ∀ j : ℕ, j < m →
          ContinuousOn T (Set.Icc (τ j) (τ (j + 1))) :=
        fun j hj => hcont j (Nat.lt_trans hj (Nat.lt_succ_self m))
      have hode' : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
          HasDerivAt T (radiatorRate C Krad (Q j) (T t)) t :=
        fun j hj => hode j (Nat.lt_trans hj (Nat.lt_succ_self m))
      have htrap' : ∀ j : ℕ, j < m → T (τ j) ∈ Set.Icc Tmin Tmax →
          ∀ t : ℝ, t ∈ Set.Icc (τ j) (τ (j + 1)) → T t ∈ Set.Icc Tmin Tmax :=
        fun j hj => htrap j (Nat.lt_trans hj (Nat.lt_succ_self m))
      have h01 : τ 0 ≤ τ m := hτ.monotone (Nat.zero_le m)
      have hτm_mem : τ m ∈ Set.Icc (τ 0) (τ m) := ⟨h01, le_rfl⟩
      have hτm_box : T (τ m) ∈ Set.Icc Tmin Tmax :=
        ih hcont' hode' htrap' h0 (τ m) hτm_mem
      rcases le_total t (τ m) with hle | hge
      · have ht' : t ∈ Set.Icc (τ 0) (τ m) := ⟨ht.1, hle⟩
        exact ih hcont' hode' htrap' h0 t ht'
      · exact htrap m (Nat.lt_succ_self m) hτm_box t ⟨hge, ht.2⟩
  exact aux m hcont hode htrap h0 t ht

/-! ## B. Battery loss heat and the mission schedule -/

/-! ### B.1. Port law and dissipated heat -/

/-- Heat dissipated in the battery (W) when it is charged with the terminal power `Pc` and
discharged with the terminal power `Pd`, with charge and discharge efficiencies `ηc` and `ηd`:
`(1 - ηc) Pc + (1 / ηd - 1) Pd`. -/
noncomputable def batteryLossHeat (ηc ηd Pc Pd : ℝ) : ℝ :=
  (1 - ηc) * Pc + (1 / ηd - 1) * Pd

/-- Port balance: the terminal power `Pc - Pd` absorbed by the battery is the storage power
`ηc Pc - Pd / ηd` plus the dissipated heat. -/
lemma terminalPower_eq_storage_add_loss (ηc ηd Pc Pd : ℝ) :
    Pc - Pd = (ηc * Pc - Pd / ηd) + batteryLossHeat ηc ηd Pc Pd := by
  unfold batteryLossHeat
  ring

/-- The dissipated heat is nonnegative for nonnegative charge and discharge powers and
efficiencies `ηc, ηd ∈ (0, 1]`. -/
lemma batteryLossHeat_nonneg {ηc ηd Pc Pd : ℝ} (hPc : 0 ≤ Pc) (hPd : 0 ≤ Pd)
    (hηc : ηc ∈ Set.Ioc 0 1) (hηd : ηd ∈ Set.Ioc 0 1) :
    0 ≤ batteryLossHeat ηc ηd Pc Pd := by
  have hc1 : ηc ≤ 1 := hηc.2
  have hd0 : 0 < ηd := hηd.1
  have hd1 : ηd ≤ 1 := hηd.2
  unfold batteryLossHeat
  have h1 : (0 : ℝ) ≤ 1 - ηc := by linarith
  have h2 : (0 : ℝ) ≤ 1 / ηd - 1 := by
    have h3 : (1 : ℝ) ≤ 1 / ηd := by
      rw [le_div_iff₀ hd0]
      linarith
    linarith
  exact add_nonneg (mul_nonneg h1 hPc) (mul_nonneg h2 hPd)

/-- With complementarity, `Pc * Pd = 0`, the charge and discharge powers are the positive and
negative parts of the terminal power `Pc - Pd`, so the storage power and the heat depend on the
terminal power only. -/
lemma battery_port_of_complementary {ηc ηd Pc Pd : ℝ} (hPc : 0 ≤ Pc) (hPd : 0 ≤ Pd)
    (hcd : Pc * Pd = 0) :
    ηc * Pc - Pd / ηd = ηc * max (Pc - Pd) 0 - max (-(Pc - Pd)) 0 / ηd ∧
      batteryLossHeat ηc ηd Pc Pd =
        (1 - ηc) * max (Pc - Pd) 0 + (1 / ηd - 1) * max (-(Pc - Pd)) 0 := by
  rcases mul_eq_zero.mp hcd with hPc0 | hPd0
  · subst hPc0
    have hm1 : max ((0 : ℝ) - Pd) 0 = 0 := max_eq_right (by linarith)
    have hm2 : max (-((0 : ℝ) - Pd)) 0 = Pd := by
      have heq : -((0 : ℝ) - Pd) = Pd := by ring
      rw [heq]
      exact max_eq_left hPd
    rw [hm1, hm2]
    constructor
    · ring
    · unfold batteryLossHeat
      ring
  · subst hPd0
    have hm1 : max (Pc - (0 : ℝ)) 0 = Pc := by
      have heq : Pc - (0 : ℝ) = Pc := by ring
      rw [heq]
      exact max_eq_left hPc
    have hm2 : max (-(Pc - (0 : ℝ))) 0 = 0 := max_eq_right (by linarith)
    rw [hm1, hm2]
    constructor
    · ring
    · unfold batteryLossHeat
      ring

/-! ### B.2. Stored energy on the mission ledger -/

/-- Stored-energy flow of schedule interval `k` (J): `dt k * (ηc Pc k - Pd k / ηd)`. -/
noncomputable def batteryFlow (ηc ηd : ℝ) (dt Pc Pd : ℕ → ℝ) (k : ℕ) : ℝ :=
  dt k * (ηc * Pc k - Pd k / ηd)

/-- The stored energy is the resource `e` of the mission ledger whose flow is the battery flow:
on every schedule interval `k` it changes by `dt k * (ηc Pc k - Pd k / ηd)`. -/
lemma stock_batteryFlow_succ {ι : Type*} {s₀ : ι → ℝ} {flow : ι → ℕ → ℝ} {e : ι} {ηc ηd : ℝ}
    {dt Pc Pd : ℕ → ℝ} (hflow : flow e = batteryFlow ηc ηd dt Pc Pd) (k : ℕ) :
    MissionLedger.stock s₀ flow e (k + 1) =
      MissionLedger.stock s₀ flow e k + dt k * (ηc * Pc k - Pd k / ηd) := by
  rw [MissionLedger.stock_succ, hflow]
  rfl

/-- Every electrical-stock prefix is checked: in a prefix-feasible ledger whose resource `e` has
the battery flow, the stored energy after every prefix `t ≤ N` of the schedule lies between the
floor raised by the reserve and the capacity. -/
lemma prefixFeasible_battery {ι : Type*} {lo hi s₀ : ι → ℝ} {r : ι → NNReal}
    {flow : ι → ℕ → ℝ} {N : ℕ} {e : ι} {ηc ηd : ℝ} {dt Pc Pd : ℕ → ℝ}
    (hflow : flow e = batteryFlow ηc ηd dt Pc Pd)
    (h : MissionLedger.PrefixFeasible lo hi r s₀ flow N) {t : ℕ} (ht : t ≤ N) :
    lo e + r e ≤ s₀ e + ∑ k ∈ Finset.range t, dt k * (ηc * Pc k - Pd k / ηd) ∧
      s₀ e + ∑ k ∈ Finset.range t, dt k * (ηc * Pc k - Pd k / ηd) ≤ hi e := by
  have h2 := h e t ht
  simp only [MissionLedger.stock, hflow, batteryFlow] at h2
  exact h2

/-! ### B.3. Battery heat in the eclipse-mode gluing -/

/-- The battery heat keeps the lower inward sign of the radiator box: if the environmental heat
input satisfies `0 ≤ Qenv - Krad * Tmin ^ 4`, so does the total heat input with the battery heat
added. -/
lemma batteryLossHeat_lower_sign {ηc ηd Pc Pd Qenv Krad Tmin : ℝ} (hPc : 0 ≤ Pc) (hPd : 0 ≤ Pd)
    (hηc : ηc ∈ Set.Ioc 0 1) (hηd : ηd ∈ Set.Ioc 0 1) (h : 0 ≤ Qenv - Krad * Tmin ^ 4) :
    0 ≤ Qenv + batteryLossHeat ηc ηd Pc Pd - Krad * Tmin ^ 4 := by
  have hq := batteryLossHeat_nonneg hPc hPd hηc hηd
  have heq : Qenv + batteryLossHeat ηc ηd Pc Pd - Krad * Tmin ^ 4 =
      (Qenv - Krad * Tmin ^ 4) + batteryLossHeat ηc ηd Pc Pd := by ring
  rw [heq]
  exact add_nonneg h hq

/-- The battery heat as a heat input of the eclipse-mode gluing: if on every piece
`[τ j, τ (j + 1)]` of a strict partition the temperature is continuous and solves the radiator
equation with the heat input `Qenv j + batteryLossHeat ηc ηd (Pc j) (Pd j)` on the open piece,
then it is continuous on the whole horizon and satisfies the integral form of that equation on
every piece. -/
lemma batteryHeat_glued {C Krad ηc ηd : ℝ} (hC : 0 < C) {m : ℕ} {τ : ℕ → ℝ} (hτ : StrictMono τ)
    {Qenv Pc Pd : ℕ → ℝ} {T : ℝ → ℝ}
    (hcont : ∀ j : ℕ, j < m → ContinuousOn T (Set.Icc (τ j) (τ (j + 1))))
    (hode : ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Ioo (τ j) (τ (j + 1)) →
      HasDerivAt T (radiatorRate C Krad (Qenv j + batteryLossHeat ηc ηd (Pc j) (Pd j)) (T t)) t) :
    ContinuousOn T (Set.Icc (τ 0) (τ m)) ∧
      ∀ j : ℕ, j < m → ∀ t : ℝ, t ∈ Set.Icc (τ j) (τ (j + 1)) →
        T t - T (τ j) = ∫ s in τ j..t,
          radiatorRate C Krad (Qenv j + batteryLossHeat ηc ηd (Pc j) (Pd j)) (T s) := by
  constructor
  · exact glued_continuous hτ hcont hode
  · intro j hj t ht
    exact glued_integral_on_piece hC hτ hcont hode hj ht

end ThermalPowerPorts
