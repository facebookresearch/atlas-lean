/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ideal square-law MOS transistor

## i. Overview

An explicitly ideal forward nMOS model in the long-channel
gradual-channel square-law approximation, without channel-length
modulation or body effect. With overdrive `u = Vgs - Vth`, drain
voltage `Vds ≥ 0` and a fixed device constant `beta > 0`, the drain
current is `0` in cutoff (`u ≤ 0`), `beta * (u * Vds - Vds^2 / 2)`
in the triode region (`0 ≤ Vds ≤ u`), and `beta * u^2 / 2` in
saturation (`Vds ≥ u`). The model is prioritized cutoff-first; the
two active formulas agree at `Vds = u`. All quantities are real
numbers after a consistent choice of units; `beta`, threshold,
geometry, mobility and temperature are fixed.

## ii. Key results

- `current_of_nonpos`, `current_of_triode`, `current_of_saturation`:
  the region formulas of the prioritized model.
- `triode_eq_saturation_at_boundary` and `current_at_boundary`: the
  active formulas agree at `Vds = u`.
- `continuousAt_u_zero`, `continuousAt_vds_boundary`,
  `continuousAt_u_boundary`, `continuousAt_joint_boundary`:
  continuity at the cutoff threshold and across the active boundary.
  No differentiability at any boundary is claimed.
- `hasDerivAt_u_triode`, `hasDerivAt_vds_triode`,
  `hasDerivAt_u_saturation`, `hasDerivAt_vds_saturation`: the
  regional transconductance `gm` and output conductance `gds` on the
  open smooth regions only.
- `idealSquareLawMOS_spec`: the bundled contract.

## iii. Table of contents

- A. The square-law current model

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: the square-law MOSFET
  current model in the triode and saturation regions and the
  regional small-signal conductances `gm` and `gds`.

## A. The square-law current model
-/

@[expose] public section

open Topology Filter Set

namespace PhyslibExt.Electronics.IdealSquareLawMOS

/-- Triode (linear-region) formula: beta*(u*Vds - Vds^2/2). -/
noncomputable def triodeCurrent (beta u Vds : ℝ) : ℝ :=
  beta * (u * Vds - Vds ^ 2 / 2)

/-- Saturation formula: beta*u^2/2. -/
noncomputable def saturationCurrent (beta u : ℝ) : ℝ :=
  beta * u ^ 2 / 2

/-- Prioritized ideal forward nMOS drain current:
cutoff 0 if u <= 0; else triode if Vds <= u; else saturation. -/
noncomputable def current (beta u Vds : ℝ) : ℝ :=
  if u ≤ 0 then 0
  else if Vds ≤ u then triodeCurrent beta u Vds
  else saturationCurrent beta u

/-- If two functions are continuous at `x` and agree there, any
if-then-else between them is continuous at `x`. -/
private lemma continuousAt_ite_of_agree {α : Type*} [PseudoMetricSpace α]
    {β : Type*} [PseudoMetricSpace β]
    (f g : α → β) (P : α → Prop) [DecidablePred P]
    (x : α) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f x = g x) :
    ContinuousAt (fun y => if P y then f y else g y) x := by
  rw [Metric.continuousAt_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy => ?_⟩
  have hy1 : dist y x < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < δ₂ := lt_of_lt_of_le hy (min_le_right _ _)
  have e1 := h₁ hy1
  have e2 := h₂ hy2
  by_cases hPy : P y <;> by_cases hPx : P x <;> simp only [hPy, hPx, ite_true, ite_false] at *
  · exact e1
  · rw [← h]; exact e1
  · rw [h]; exact e2
  · exact e2

/-- Nonnegativity of current, as a helper before its pinned use. -/
private lemma current_nonneg_aux (beta u Vds : ℝ) (hbeta : 0 < beta)
    (hV : 0 ≤ Vds) :
    0 ≤ current beta u Vds := by
  unfold current
  by_cases hu0 : u ≤ 0
  · simp [hu0]
  · simp only [hu0, ite_false]
    by_cases hVu : Vds ≤ u
    · simp only [hVu, ite_true]
      unfold triodeCurrent
      have h1 : 0 ≤ Vds * (u - Vds) := mul_nonneg hV (sub_nonneg.mpr hVu)
      have h2 : 0 ≤ Vds ^ 2 / 2 := by positivity
      have heq : u * Vds - Vds ^ 2 / 2 = Vds * (u - Vds) + Vds ^ 2 / 2 := by ring
      have h3 : 0 ≤ u * Vds - Vds ^ 2 / 2 := by linarith
      exact mul_nonneg hbeta.le h3
    · simp only [hVu, ite_false]
      unfold saturationCurrent
      positivity

/-- Cutoff region: u <= 0 gives current 0, with priority over all
other branches. -/
lemma current_of_nonpos (beta u Vds : ℝ) (hu : u ≤ 0) :
    current beta u Vds = 0 := by
  simp [current, hu]

/-- Triode region: 0 <= Vds <= u with u > 0 gives
beta*(u*Vds - Vds^2/2). -/
lemma current_of_triode (beta u Vds : ℝ) (hu : 0 < u)
    (hV0 : 0 ≤ Vds) (hVu : Vds ≤ u) :
    current beta u Vds = triodeCurrent beta u Vds := by
  have _ : 0 ≤ Vds := hV0
  have h1 : ¬ u ≤ 0 := by linarith
  simp [current, h1, hVu]

/-- Saturation region value: u > 0 and u <= Vds gives beta*u^2/2.
At Vds = u this is the common boundary value; the definition itself
selects the triode branch there. -/
lemma current_of_saturation (beta u Vds : ℝ) (hu : 0 < u)
    (hVu : u ≤ Vds) :
    current beta u Vds = saturationCurrent beta u := by
  have h1 : ¬ u ≤ 0 := by linarith
  unfold current
  simp only [h1, ite_false]
  by_cases h : Vds ≤ u
  · simp only [h, ite_true]
    have hVu_eq : Vds = u := le_antisymm h hVu
    subst hVu_eq
    unfold triodeCurrent saturationCurrent
    ring
  · simp [h]

/-- Both active formulas agree at Vds = u:
beta*(u*u - u^2/2) = beta*u^2/2. -/
lemma triode_eq_saturation_at_boundary (beta u : ℝ) :
    triodeCurrent beta u u = saturationCurrent beta u := by
  unfold triodeCurrent saturationCurrent
  ring

/-- At the active boundary the device current is the common value
of the two active formulas. -/
lemma current_at_boundary (beta u : ℝ) (hu : 0 < u) :
    current beta u u = triodeCurrent beta u u
      ∧ current beta u u = saturationCurrent beta u := by
  constructor
  · exact current_of_triode beta u u hu hu.le le_rfl
  · exact current_of_saturation beta u u hu le_rfl

/-- Continuity in u at cutoff onset u = 0, for fixed Vds >= 0:
both sides approach the cutoff value 0. -/
lemma continuousAt_u_zero (beta Vds : ℝ) (hbeta : 0 < beta)
    (hV : 0 ≤ Vds) :
    ContinuousAt (fun u : ℝ => current beta u Vds) 0 := by
  have hval : current beta 0 Vds = 0 := current_of_nonpos beta 0 Vds le_rfl
  have hcont : ContinuousAt (fun u : ℝ => beta * u ^ 2 / 2) 0 := by fun_prop
  have htend : Filter.Tendsto (fun u : ℝ => beta * u ^ 2 / 2) (nhds 0) (nhds 0) := by
    simpa using hcont.tendsto
  have hsqueeze : Filter.Tendsto (fun u => current beta u Vds) (nhds 0) (nhds 0) := by
    apply squeeze_zero (fun u => current_nonneg_aux beta u Vds hbeta hV) (fun u => ?_) htend
    by_cases hu0 : u ≤ 0
    · rw [current_of_nonpos beta u Vds hu0]
      positivity
    · have hu0' : 0 < u := not_le.mp hu0
      by_cases hVu : Vds ≤ u
      · rw [current_of_triode beta u Vds hu0' hV hVu]
        unfold triodeCurrent
        have hsq : 0 ≤ (u - Vds) ^ 2 := sq_nonneg _
        have hbeta2 : 0 ≤ beta * (u - Vds) ^ 2 / 2 := by positivity
        have heq : beta * (u * Vds - Vds ^ 2 / 2) = beta * u ^ 2 / 2 - beta * (u - Vds) ^ 2 / 2 := by ring
        linarith
      · have hVu' : u ≤ Vds := le_of_not_ge hVu
        rw [current_of_saturation beta u Vds hu0' hVu']
        unfold saturationCurrent
        exact le_rfl
  show Filter.Tendsto _ (nhds 0) (nhds (current beta 0 Vds))
  rw [hval]
  exact hsqueeze

/-- Continuity in Vds across the active boundary Vds = u, u fixed. -/
lemma continuousAt_vds_boundary (beta u : ℝ) (hbeta : 0 < beta)
    (hu : 0 < u) :
    ContinuousAt (fun Vds : ℝ => current beta u Vds) u := by
  have _ : 0 < beta := hbeta
  have h1 : ¬ u ≤ 0 := by linarith
  have htri : ContinuousAt (fun V : ℝ => triodeCurrent beta u V) u := by
    unfold triodeCurrent
    fun_prop
  have hsat : ContinuousAt (fun _ : ℝ => saturationCurrent beta u) u :=
    continuousAt_const
  have hagree : triodeCurrent beta u u = saturationCurrent beta u :=
    triode_eq_saturation_at_boundary beta u
  have heq : (fun Vds' : ℝ => current beta u Vds') =
      (fun Vds' : ℝ => if Vds' ≤ u then triodeCurrent beta u Vds' else saturationCurrent beta u) := by
    funext V
    unfold current
    simp [h1]
  rw [heq]
  exact continuousAt_ite_of_agree _ _ (fun V => V ≤ u) _ htri hsat hagree

/-- Continuity in u across the active boundary u = Vds, Vds > 0 fixed. -/
lemma continuousAt_u_boundary (beta Vds : ℝ) (hbeta : 0 < beta)
    (hV : 0 < Vds) :
    ContinuousAt (fun u : ℝ => current beta u Vds) Vds := by
  have _ : 0 < beta := hbeta
  have htri : ContinuousAt (fun u' : ℝ => triodeCurrent beta u' Vds) Vds := by
    unfold triodeCurrent
    fun_prop
  have hsat : ContinuousAt (fun u' : ℝ => saturationCurrent beta u') Vds := by
    unfold saturationCurrent
    fun_prop
  have hagree : triodeCurrent beta Vds Vds = saturationCurrent beta Vds :=
    triode_eq_saturation_at_boundary beta Vds
  have hgcont : ContinuousAt (fun u' : ℝ => if Vds ≤ u' then triodeCurrent beta u' Vds else saturationCurrent beta u') Vds :=
    continuousAt_ite_of_agree _ _ (fun u' => Vds ≤ u') _ htri hsat hagree
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds Vds := Ioi_mem_nhds hV
  have heq : (fun u' : ℝ => current beta u' Vds) =ᶠ[nhds Vds]
      (fun u' : ℝ => if Vds ≤ u' then triodeCurrent beta u' Vds else saturationCurrent beta u') := by
    filter_upwards [hmem] with u' hu'
    have hu0 : (0 : ℝ) < u' := hu'
    have h1 : ¬ u' ≤ 0 := by linarith
    unfold current
    simp [h1]
  exact hgcont.congr_of_eventuallyEq heq

/-- Joint continuity in (u, Vds) across the active boundary at (u, u). -/
lemma continuousAt_joint_boundary (beta u : ℝ) (hbeta : 0 < beta)
    (hu : 0 < u) :
    ContinuousAt (fun p : ℝ × ℝ => current beta p.1 p.2) (u, u) := by
  have _ : 0 < beta := hbeta
  have htri : ContinuousAt (fun p : ℝ × ℝ => triodeCurrent beta p.1 p.2) (u, u) := by
    unfold triodeCurrent
    fun_prop
  have hsat : ContinuousAt (fun p : ℝ × ℝ => saturationCurrent beta p.1) (u, u) := by
    unfold saturationCurrent
    fun_prop
  have hagree : triodeCurrent beta u u = saturationCurrent beta u :=
    triode_eq_saturation_at_boundary beta u
  have hgcont : ContinuousAt (fun p : ℝ × ℝ => if p.2 ≤ p.1 then triodeCurrent beta p.1 p.2 else saturationCurrent beta p.1) (u, u) :=
    continuousAt_ite_of_agree _ _ (fun p : ℝ × ℝ => p.2 ≤ p.1) _ htri hsat hagree
  have hfst : Filter.Tendsto (fun p : ℝ × ℝ => p.1) (nhds (u, u)) (nhds u) :=
    continuous_fst.tendsto (u, u)
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds u := Ioi_mem_nhds hu
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (u, u), p.1 ∈ Set.Ioi (0 : ℝ) :=
    hfst.eventually (Filter.eventually_of_mem hmem (fun y hy => hy))
  have heq : (fun p : ℝ × ℝ => current beta p.1 p.2) =ᶠ[nhds (u, u)]
      (fun p : ℝ × ℝ => if p.2 ≤ p.1 then triodeCurrent beta p.1 p.2 else saturationCurrent beta p.1) := by
    filter_upwards [hev] with p hp
    have hp0 : (0 : ℝ) < p.1 := hp
    have h1 : ¬ p.1 ≤ 0 := by linarith
    unfold current
    simp [h1]
  exact hgcont.congr_of_eventuallyEq heq

/-- Cutoff interior, gm: derivative in u is 0 for u < 0. -/
lemma hasDerivAt_u_cutoff (beta u Vds : ℝ) (hu : u < 0) :
    HasDerivAt (fun u' : ℝ => current beta u' Vds) 0 u := by
  have hmem : Set.Iio (0 : ℝ) ∈ nhds u := Iio_mem_nhds hu
  have heq : (fun u' : ℝ => current beta u' Vds) =ᶠ[nhds u] (fun _ => 0) := by
    filter_upwards [hmem] with u' hu'
    have hu0 : u' < 0 := hu'
    exact current_of_nonpos beta u' Vds hu0.le
  exact (hasDerivAt_const u 0).congr_of_eventuallyEq heq

/-- Cutoff interior, gds: derivative in Vds is 0 for u < 0. -/
lemma hasDerivAt_vds_cutoff (beta u Vds : ℝ) (hu : u < 0) :
    HasDerivAt (fun V : ℝ => current beta u V) 0 Vds := by
  have heq : (fun V : ℝ => current beta u V) = fun _ => 0 :=
    funext fun V => current_of_nonpos beta u V hu.le
  rw [heq]
  exact hasDerivAt_const Vds 0

/-- Triode interior, gm: derivative in u is beta*Vds
for 0 < Vds < u. -/
lemma hasDerivAt_u_triode (beta u Vds : ℝ) (hV : 0 < Vds)
    (hVu : Vds < u) :
    HasDerivAt (fun u' : ℝ => current beta u' Vds) (beta * Vds) u := by
  have hmem : Set.Ioi Vds ∈ nhds u := Ioi_mem_nhds hVu
  have heq : (fun u' : ℝ => current beta u' Vds) =ᶠ[nhds u]
      (fun u' : ℝ => triodeCurrent beta u' Vds) := by
    filter_upwards [hmem] with u' hu'
    have huV : Vds < u' := hu'
    exact current_of_triode beta u' Vds (lt_trans hV huV) hV.le huV.le
  have h1 : HasDerivAt (fun u' : ℝ => u' * Vds) Vds u := by
    simpa using (hasDerivAt_id u).mul_const Vds
  have h2 : HasDerivAt (fun u' : ℝ => u' * Vds - Vds ^ 2 / 2) Vds u :=
    h1.sub_const (Vds ^ 2 / 2)
  have h3 : HasDerivAt (fun u' : ℝ => beta * (u' * Vds - Vds ^ 2 / 2)) (beta * Vds) u :=
    h2.const_mul beta
  have htri : HasDerivAt (fun u' : ℝ => triodeCurrent beta u' Vds) (beta * Vds) u := by
    simpa [triodeCurrent] using h3
  exact htri.congr_of_eventuallyEq heq

/-- Triode interior, gds: derivative in Vds is beta*(u - Vds)
for 0 < Vds < u. -/
lemma hasDerivAt_vds_triode (beta u Vds : ℝ) (hV : 0 < Vds)
    (hVu : Vds < u) :
    HasDerivAt (fun V : ℝ => current beta u V) (beta * (u - Vds)) Vds := by
  have hu_pos : 0 < u := lt_trans hV hVu
  have hmem : Set.Ioo (0 : ℝ) u ∈ nhds Vds := Ioo_mem_nhds hV hVu
  have heq : (fun V : ℝ => current beta u V) =ᶠ[nhds Vds]
      (fun V : ℝ => triodeCurrent beta u V) := by
    filter_upwards [hmem] with V hV'
    have h0V : 0 < V := hV'.1
    have hVu' : V < u := hV'.2
    exact current_of_triode beta u V hu_pos h0V.le hVu'.le
  have h1 : HasDerivAt (fun V : ℝ => u * V) u Vds := by
    simpa using (hasDerivAt_id Vds).const_mul u
  have hpow : HasDerivAt (fun V : ℝ => V ^ 2) (2 * Vds) Vds := by
    have hp := hasDerivAt_pow 2 Vds
    simpa using hp
  have h2 : HasDerivAt (fun V : ℝ => V ^ 2 / 2) Vds Vds := by
    have hd := hpow.div_const (2 : ℝ)
    simpa using hd
  have hsub : HasDerivAt (fun V : ℝ => u * V - V ^ 2 / 2) (u - Vds) Vds := by
    have hs := h1.sub h2
    simpa [Pi.sub_def] using hs
  have h3 : HasDerivAt (fun V : ℝ => beta * (u * V - V ^ 2 / 2)) (beta * (u - Vds)) Vds :=
    hsub.const_mul beta
  have htri : HasDerivAt (fun V : ℝ => triodeCurrent beta u V) (beta * (u - Vds)) Vds := by
    simpa [triodeCurrent] using h3
  exact htri.congr_of_eventuallyEq heq

/-- Saturation interior, gm: derivative in u is beta*u
for 0 < u < Vds. -/
lemma hasDerivAt_u_saturation (beta u Vds : ℝ) (hu : 0 < u)
    (hVu : u < Vds) :
    HasDerivAt (fun u' : ℝ => current beta u' Vds) (beta * u) u := by
  have hmem : Set.Ioo (0 : ℝ) Vds ∈ nhds u := Ioo_mem_nhds hu hVu
  have heq : (fun u' : ℝ => current beta u' Vds) =ᶠ[nhds u]
      (fun u' : ℝ => saturationCurrent beta u') := by
    filter_upwards [hmem] with u' hu'
    have h0u : 0 < u' := hu'.1
    have huV : u' < Vds := hu'.2
    exact current_of_saturation beta u' Vds h0u huV.le
  have hpow : HasDerivAt (fun u' : ℝ => u' ^ 2) (2 * u) u := by
    have hp := hasDerivAt_pow 2 u
    simpa using hp
  have hdiv : HasDerivAt (fun u' : ℝ => u' ^ 2 / 2) u u := by
    have hd := hpow.div_const (2 : ℝ)
    simpa using hd
  have h3 : HasDerivAt (fun u' : ℝ => beta * (u' ^ 2 / 2)) (beta * u) u :=
    hdiv.const_mul beta
  have hsat : HasDerivAt (fun u' : ℝ => saturationCurrent beta u') (beta * u) u := by
    simp only [saturationCurrent]
    simpa [mul_div_assoc] using h3
  exact hsat.congr_of_eventuallyEq heq

/-- Saturation interior, gds: derivative in Vds is 0
for 0 < u < Vds. -/
lemma hasDerivAt_vds_saturation (beta u Vds : ℝ) (hu : 0 < u)
    (hVu : u < Vds) :
    HasDerivAt (fun V : ℝ => current beta u V) 0 Vds := by
  have hmem : Set.Ioi u ∈ nhds Vds := Ioi_mem_nhds hVu
  have heq : (fun V : ℝ => current beta u V) =ᶠ[nhds Vds] (fun _ => saturationCurrent beta u) := by
    filter_upwards [hmem] with V hV'
    have huV : u < V := hV'
    exact current_of_saturation beta u V hu huV.le
  have hconst : HasDerivAt (fun _ : ℝ => saturationCurrent beta u) 0 Vds :=
    hasDerivAt_const Vds (saturationCurrent beta u)
  exact hconst.congr_of_eventuallyEq heq

/-- Triode gds is nonnegative on the closed triode region:
0 <= beta*(u - Vds) when beta > 0 and Vds <= u. -/
lemma triode_gds_nonneg (beta u Vds : ℝ) (hbeta : 0 < beta)
    (hVu : Vds ≤ u) :
    0 ≤ beta * (u - Vds) := by
  exact mul_nonneg hbeta.le (sub_nonneg.mpr hVu)

/-- Drain current is nonnegative on the forward domain Vds >= 0. -/
lemma current_nonneg (beta u Vds : ℝ) (hbeta : 0 < beta)
    (hV : 0 ≤ Vds) :
    0 ≤ current beta u Vds := by
  exact current_nonneg_aux beta u Vds hbeta hV

/-- Ideal long-channel square-law nMOS, bundled: prioritized piecewise
current, boundary agreement, continuity at u = 0 and across Vds = u,
regional gm/gds on open regions, nonnegative triode gds, and
nonnegative current on Vds >= 0. No derivative at any boundary and
no global smoothness is asserted. -/
lemma idealSquareLawMOS_spec (beta : ℝ) (hbeta : 0 < beta) :
    (∀ u Vds : ℝ, 0 ≤ Vds → u ≤ 0 → current beta u Vds = 0)
    ∧ (∀ u Vds : ℝ, 0 ≤ Vds → 0 < u → Vds ≤ u →
        current beta u Vds = triodeCurrent beta u Vds)
    ∧ (∀ u Vds : ℝ, 0 < u → u ≤ Vds →
        current beta u Vds = saturationCurrent beta u)
    ∧ (∀ u : ℝ, triodeCurrent beta u u = saturationCurrent beta u)
    ∧ (∀ Vds : ℝ, 0 ≤ Vds →
        ContinuousAt (fun u : ℝ => current beta u Vds) 0)
    ∧ (∀ u : ℝ, 0 < u →
        ContinuousAt (fun Vds : ℝ => current beta u Vds) u)
    ∧ (∀ u : ℝ, 0 < u →
        ContinuousAt (fun p : ℝ × ℝ => current beta p.1 p.2) (u, u))
    ∧ (∀ u Vds : ℝ, u < 0 →
        HasDerivAt (fun u' : ℝ => current beta u' Vds) 0 u)
    ∧ (∀ u Vds : ℝ, u < 0 →
        HasDerivAt (fun V : ℝ => current beta u V) 0 Vds)
    ∧ (∀ u Vds : ℝ, 0 < Vds → Vds < u →
        HasDerivAt (fun u' : ℝ => current beta u' Vds) (beta * Vds) u)
    ∧ (∀ u Vds : ℝ, 0 < Vds → Vds < u →
        HasDerivAt (fun V : ℝ => current beta u V) (beta * (u - Vds)) Vds)
    ∧ (∀ u Vds : ℝ, 0 < u → u < Vds →
        HasDerivAt (fun u' : ℝ => current beta u' Vds) (beta * u) u)
    ∧ (∀ u Vds : ℝ, 0 < u → u < Vds →
        HasDerivAt (fun V : ℝ => current beta u V) 0 Vds)
    ∧ (∀ u Vds : ℝ, Vds ≤ u → 0 ≤ beta * (u - Vds))
    ∧ (∀ u Vds : ℝ, 0 ≤ Vds → 0 ≤ current beta u Vds) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u Vds _ hu
    exact current_of_nonpos beta u Vds hu
  · intro u Vds hV hu hVu
    exact current_of_triode beta u Vds hu hV hVu
  · intro u Vds hu hVu
    exact current_of_saturation beta u Vds hu hVu
  · intro u
    exact triode_eq_saturation_at_boundary beta u
  · intro Vds hV
    exact continuousAt_u_zero beta Vds hbeta hV
  · intro u hu
    exact continuousAt_vds_boundary beta u hbeta hu
  · intro u hu
    exact continuousAt_joint_boundary beta u hbeta hu
  · intro u Vds hu
    exact hasDerivAt_u_cutoff beta u Vds hu
  · intro u Vds hu
    exact hasDerivAt_vds_cutoff beta u Vds hu
  · intro u Vds hV hVu
    exact hasDerivAt_u_triode beta u Vds hV hVu
  · intro u Vds hV hVu
    exact hasDerivAt_vds_triode beta u Vds hV hVu
  · intro u Vds hu hVu
    exact hasDerivAt_u_saturation beta u Vds hu hVu
  · intro u Vds hu hVu
    exact hasDerivAt_vds_saturation beta u Vds hu hVu
  · intro u Vds hVu
    exact triode_gds_nonneg beta u Vds hbeta hVu
  · intro u Vds hV
    exact current_nonneg beta u Vds hbeta hV

end PhyslibExt.Electronics.IdealSquareLawMOS
