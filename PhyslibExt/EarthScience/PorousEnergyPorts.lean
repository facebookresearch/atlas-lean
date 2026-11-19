/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibExt.EarthScience.ThiemWellFlow

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial Darcy head profile on an annulus

The steady radial Darcy discharge of a confined aquifer integrates to the logarithmic head
profile on an annulus around a well; with the sign of its rate reversed, this is the Thiem
profile.

## i. Overview

A confined aquifer of constant transmissivity `Tr > 0` (hydraulic conductivity times aquifer
thickness) carries steady single-phase radial flow on the annulus `r0 ≤ r ≤ r1` around a well
of radius `r0 > 0`. Darcy's law is a constitutive input, not a derived fluid law: integrated
over the aquifer thickness and the circle of radius `r`, it gives the outward volumetric
discharge `Q = -2 π r Tr h'(r)` for the hydraulic head `h`. In steady flow without recharge in
the annulus the discharge is the same at every radius; `Q > 0` is injection and `Q < 0` is
extraction. Integrating `h' = -Q / (2 π Tr r)` gives
`h r - h r0 = -Q log (r / r0) / (2 π Tr)`.

The Thiem head difference `EarthScience.thiem_head_difference` is written for the profile
`C + Q log r / (2 π T)` with the pumping (extraction) rate `Q`, which is the negative of the
outward discharge: the profile with rate `P` has outward discharge `-P`. With the rate `-Q`
the Thiem head difference is exactly the radial Darcy head difference.

A zero well radius admits no head that stays finite at the axis with a nonzero discharge, and
a negative transmissivity sends the discharge up the head gradient; both inputs are rejected.
Multiphase flow, unconfined aquifers, leakage, recharge and transient storage are not treated.

## ii. Key results

- `EarthScience.radialDarcy_head_sub`: the radial Darcy head difference on the annulus.
- `EarthScience.radialDarcyHead_solves`: the logarithmic profile solves the model for every
  discharge.
- `EarthScience.thiemProfile_outward_discharge`: the Thiem rate is minus the outward
  discharge.
- `EarthScience.radialDarcy_head_sub_eq_thiem`: the head difference is the Thiem head
  difference for the pumping rate `-Q`.
- `EarthScience.radialDarcy_no_head_at_axis`: a zero well radius is rejected.
- `EarthScience.radialDischarge_upgradient_of_neg`: a negative transmissivity is rejected.

## iii. Table of contents

- A. Radial Darcy head profile
- B. Matching the Thiem profile
- C. Rejected inputs

## iv. References

- J. Bear, *Dynamics of Fluids in Porous Media*, American Elsevier (1972): Darcy's law and
  steady radial flow to a well in a confined aquifer.
- `EarthScience.thiem_head_difference` (`PhyslibExt.EarthScience.ThiemWellFlow`).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Radial Darcy head profile -/

/-- Radial Darcy head profile with head `h0` at the well radius `r0`, constant outward
discharge `Q` and transmissivity `Tr`: `h0 - Q log (r / r0) / (2 π Tr)`. -/
noncomputable def radialDarcyHead (h0 Q Tr r0 r : ℝ) : ℝ :=
  h0 - Q * Real.log (r / r0) / (2 * Real.pi * Tr)

/-- Radial Darcy head difference on the annulus `r0 ≤ r ≤ r1` with `r0 > 0` and constant
transmissivity `Tr > 0`. If the head `h` is continuous on the closed annulus, has radial
derivative `h'` inside it, and the steady outward discharge `Q = -2 π r Tr h'(r)` is the same
at every interior radius, then `h r - h r0 = -Q log (r / r0) / (2 π Tr)` on the closed
annulus. -/
lemma radialDarcy_head_sub {h h' : ℝ → ℝ} {Q Tr r0 r1 : ℝ} (hr0 : 0 < r0) (hTr : 0 < Tr)
    (hcont : ContinuousOn h (Set.Icc r0 r1))
    (hderiv : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo r0 r1, Q = -2 * Real.pi * r * Tr * h' r) :
    ∀ r ∈ Set.Icc r0 r1, h r - h r0 = -Q * Real.log (r / r0) / (2 * Real.pi * Tr) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0' : r0 ≠ 0 := ne_of_gt hr0
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  have h2Tr : (2 * Real.pi * Tr) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hTr'
  intro r hr
  have hr0r : r0 ≤ r := hr.1
  have hrr1 : r ≤ r1 := hr.2
  by_cases heq : r = r0
  · rw [heq]
    simp only [sub_self]
    have hdiv : r0 / r0 = 1 := by field_simp
    rw [hdiv, Real.log_one]
    simp
  · have hlt : r0 < r := lt_of_le_of_ne hr0r (fun h => heq h.symm)
    have hrne : r - r0 ≠ 0 := by
      apply ne_of_gt
      linarith
    have hrpos : 0 < r := lt_trans hr0 hlt
    have hr' : r ≠ 0 := ne_of_gt hrpos
    have hsub1 : Set.Icc r0 r ⊆ Set.Icc r0 r1 :=
      Set.Icc_subset_Icc_right hrr1
    have hsub0 : Set.Icc r0 r ⊆ {0}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hx0 : r0 ≤ x := hx.1
      have : 0 < x := lt_of_lt_of_le hr0 hx0
      exact ne_of_gt this
    have hcont_h : ContinuousOn h (Set.Icc r0 r) := hcont.mono hsub1
    have hcont_log : ContinuousOn Real.log (Set.Icc r0 r) :=
      Real.continuousOn_log.mono hsub0
    have hcont_Qlog : ContinuousOn (fun s : ℝ => Q * Real.log s) (Set.Icc r0 r) :=
      hcont_log.const_mul Q
    have hcont_g2 :
        ContinuousOn (fun s : ℝ => Q * Real.log s / (2 * Real.pi * Tr)) (Set.Icc r0 r) :=
      hcont_Qlog.div_const (2 * Real.pi * Tr)
    have hcont_g :
        ContinuousOn (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) (Set.Icc r0 r) :=
      hcont_h.add hcont_g2
    have hderiv_zero : ∀ x ∈ Set.Ioo r0 r,
        HasDerivAt (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) 0 x := by
      intro x hx
      have hx0 : r0 < x := hx.1
      have hxx : x < r := hx.2
      have hxpos : 0 < x := lt_trans hr0 hx0
      have hx' : x ≠ 0 := ne_of_gt hxpos
      have hx1 : x ∈ Set.Ioo r0 r1 := ⟨hx0, lt_of_lt_of_le hxx hrr1⟩
      have hh : HasDerivAt h (h' x) x := hderiv x hx1
      have hQx : Q = -2 * Real.pi * x * Tr * h' x := hQ x hx1
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx'
      have hQm : HasDerivAt (fun s : ℝ => Q * Real.log s) (Q * x⁻¹) x :=
        hlog.const_mul Q
      have hdiv2 : HasDerivAt (fun s : ℝ => Q * Real.log s / (2 * Real.pi * Tr))
          ((Q * x⁻¹) / (2 * Real.pi * Tr)) x :=
        hQm.div_const (2 * Real.pi * Tr)
      have heq2 : (Q * x⁻¹) / (2 * Real.pi * Tr) = Q / (2 * Real.pi * Tr * x) := by
        field_simp
      rw [heq2] at hdiv2
      have hadd : HasDerivAt (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr))
          (h' x + Q / (2 * Real.pi * Tr * x)) x :=
        hh.add hdiv2
      have hzero : h' x + Q / (2 * Real.pi * Tr * x) = 0 := by
        rw [hQx]
        field_simp
        ring
      rw [hzero] at hadd
      exact hadd
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope
      (fun s : ℝ => h s + Q * Real.log s / (2 * Real.pi * Tr)) (fun _ => 0) hlt hcont_g hderiv_zero
    have hg_eq : (h r + Q * Real.log r / (2 * Real.pi * Tr)) -
        (h r0 + Q * Real.log r0 / (2 * Real.pi * Tr)) = 0 := by
      have h1 : ((h r + Q * Real.log r / (2 * Real.pi * Tr)) -
          (h r0 + Q * Real.log r0 / (2 * Real.pi * Tr))) / (r - r0) = 0 := by
        have := hc_eq.symm
        simpa using this
      have h2 := div_eq_zero_iff.mp h1
      rcases h2 with hnum | hden
      · exact hnum
      · exact absurd hden hrne
    have hlogdiv : Real.log (r / r0) = Real.log r - Real.log r0 :=
      Real.log_div hr' hr0'
    rw [hlogdiv]
    have hfield : h r - h r0 = -Q * (Real.log r - Real.log r0) / (2 * Real.pi * Tr) := by
      have h3 := hg_eq
      field_simp at h3 ⊢
      linarith
    exact hfield

/-- The radial Darcy profile solves the model for every discharge `Q`: at each radius `r > 0`
its radial derivative is `-Q / (2 π Tr r)`, and its outward discharge is `Q`. -/
lemma radialDarcyHead_solves {h0 Q Tr r0 r : ℝ} (hr0 : 0 < r0) (hTr : 0 < Tr) (hr : 0 < r) :
    HasDerivAt (radialDarcyHead h0 Q Tr r0) (-Q / (2 * Real.pi * Tr * r)) r ∧
      -2 * Real.pi * r * Tr * (-Q / (2 * Real.pi * Tr * r)) = Q := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0' : r0 ≠ 0 := ne_of_gt hr0
  have hr' : r ≠ 0 := ne_of_gt hr
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  constructor
  · have h1 : HasDerivAt (fun s : ℝ => s / r0) (1 / r0) r :=
      (hasDerivAt_id r).div_const r0
    have hne : r / r0 ≠ 0 := by
      apply ne_of_gt
      positivity
    have hlog : HasDerivAt (fun s : ℝ => Real.log (s / r0)) ((1 / r0) / (r / r0)) r :=
      h1.log hne
    have hQ : HasDerivAt (fun s : ℝ => Q * Real.log (s / r0)) (Q * ((1 / r0) / (r / r0))) r :=
      hlog.const_mul Q
    have hdiv : HasDerivAt (fun s : ℝ => Q * Real.log (s / r0) / (2 * Real.pi * Tr))
        ((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr)) r :=
      hQ.div_const (2 * Real.pi * Tr)
    have hsub : HasDerivAt (fun s : ℝ => h0 - Q * Real.log (s / r0) / (2 * Real.pi * Tr))
        (-((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr))) r :=
      hdiv.const_sub h0
    have heq :
        -((Q * ((1 / r0) / (r / r0))) / (2 * Real.pi * Tr)) = -Q / (2 * Real.pi * Tr * r) := by
      field_simp
    rw [heq] at hsub
    exact hsub
  · field_simp

/-! ## B. Matching the Thiem profile -/

/-- The Thiem rate is the pumping (extraction) rate: the Thiem profile
`C + P log r / (2 π Tr)` with rate `P` has radial derivative `P / (2 π Tr r)` at `r > 0`, so
its outward discharge `-2 π r Tr h'(r)` is `-P`. -/
lemma thiemProfile_outward_discharge {P Tr C r : ℝ} (hTr : 0 < Tr) (hr : 0 < r) :
    HasDerivAt (fun s => C + P * Real.log s / (2 * Real.pi * Tr))
        (P / (2 * Real.pi * Tr * r)) r ∧
      -2 * Real.pi * r * Tr * (P / (2 * Real.pi * Tr * r)) = -P := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr' : r ≠ 0 := ne_of_gt hr
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  constructor
  · have hlog : HasDerivAt Real.log r⁻¹ r := Real.hasDerivAt_log hr'
    have hP : HasDerivAt (fun s : ℝ => P * Real.log s) (P * r⁻¹) r :=
      hlog.const_mul P
    have hdiv : HasDerivAt (fun s : ℝ => P * Real.log s / (2 * Real.pi * Tr))
        ((P * r⁻¹) / (2 * Real.pi * Tr)) r :=
      hP.div_const (2 * Real.pi * Tr)
    have hadd : HasDerivAt (fun s : ℝ => C + P * Real.log s / (2 * Real.pi * Tr))
        ((P * r⁻¹) / (2 * Real.pi * Tr)) r :=
      hdiv.const_add C
    have heq : (P * r⁻¹) / (2 * Real.pi * Tr) = P / (2 * Real.pi * Tr * r) := by
      field_simp
    rw [heq] at hadd
    exact hadd
  · field_simp

/-- Matching the Thiem profile with the sign reversed: on the annulus, the radial Darcy head
difference equals the Thiem head difference of `EarthScience.thiem_head_difference` for the
pumping rate `-Q`, with any additive constant `C`. -/
lemma radialDarcy_head_sub_eq_thiem {h h' : ℝ → ℝ} {Q Tr r0 r1 : ℝ} (hr0 : 0 < r0)
    (hTr : 0 < Tr) (hcont : ContinuousOn h (Set.Icc r0 r1))
    (hderiv : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo r0 r1, Q = -2 * Real.pi * r * Tr * h' r) (C : ℝ) :
    ∀ r ∈ Set.Icc r0 r1, h r - h r0 =
      (C + -Q * Real.log r / (2 * Real.pi * Tr)) -
        (C + -Q * Real.log r0 / (2 * Real.pi * Tr)) := by
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr0 hr.1
  have hmain : h r - h r0 = -Q * Real.log (r / r0) / (2 * Real.pi * Tr) :=
    radialDarcy_head_sub hr0 hTr hcont hderiv hQ r hr
  have hthiem : (C + -Q * Real.log r / (2 * Real.pi * Tr)) -
      (C + -Q * Real.log r0 / (2 * Real.pi * Tr)) =
      -Q * Real.log (r / r0) / (2 * Real.pi * Tr) :=
    thiem_head_difference hTr' hr0 hrpos
  exact hmain.trans hthiem.symm

/-! ## C. Rejected inputs -/

/-- A zero well radius is rejected: for `Tr > 0`, `r1 > 0` and a nonzero discharge `Q`, no head
continuous on `[0, r1]` satisfies the radial Darcy discharge relation on `(0, r1)`, because
the logarithmic profile is unbounded at the axis. -/
lemma radialDarcy_no_head_at_axis {h h' : ℝ → ℝ} {Q Tr r1 : ℝ} (hTr : 0 < Tr) (hr1 : 0 < r1)
    (hQ0 : Q ≠ 0) (hcont : ContinuousOn h (Set.Icc 0 r1))
    (hderiv : ∀ r ∈ Set.Ioo 0 r1, HasDerivAt h (h' r) r)
    (hQ : ∀ r ∈ Set.Ioo 0 r1, Q = -2 * Real.pi * r * Tr * h' r) :
    False := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hMabs : ∀ x ∈ Set.Icc 0 r1, |h x| ≤ M := by
    intro x hx
    have hle := hM x hx
    rwa [Real.norm_eq_abs] at hle
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 r1 := ⟨le_refl 0, le_of_lt hr1⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMabs 0 h0mem)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hTr' : Tr ≠ 0 := ne_of_gt hTr
  have hQabs : 0 < |Q| := abs_pos.mpr hQ0
  have hQabs_ne : |Q| ≠ 0 := ne_of_gt hQabs
  have hden_pos : 0 < 2 * Real.pi * Tr := by positivity
  have hden_ne : (2 * Real.pi * Tr) ≠ 0 := ne_of_gt hden_pos
  set K : ℝ := (2 * M + 1) * (2 * Real.pi * Tr) / |Q| with hKdef
  have hKpos : 0 < K := by
    have h1 : 0 < 2 * M + 1 := by linarith
    have hnum : 0 < (2 * M + 1) * (2 * Real.pi * Tr) := mul_pos h1 hden_pos
    rw [hKdef]
    exact div_pos hnum hQabs
  have hexp_pos : 0 < Real.exp (-K) := Real.exp_pos _
  have hexp_ne : Real.exp (-K) ≠ 0 := ne_of_gt hexp_pos
  set r : ℝ := r1 * Real.exp (-K) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact mul_pos hr1 hexp_pos
  have hr0le : 0 ≤ r := le_of_lt hrpos
  have hexp_lt : Real.exp (-K) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hrr1 : r < r1 := by
    have hmul : r1 * Real.exp (-K) < r1 * 1 :=
      mul_lt_mul_of_pos_left hexp_lt hr1
    rw [mul_one] at hmul
    rw [hrdef]
    exact hmul
  have hrle : r ≤ r1 := le_of_lt hrr1
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hr1ne : r1 ≠ 0 := ne_of_gt hr1
  have hsubIcc : Set.Icc r r1 ⊆ Set.Icc 0 r1 :=
    Set.Icc_subset_Icc_left hr0le
  have hcont' : ContinuousOn h (Set.Icc r r1) := hcont.mono hsubIcc
  have hderiv' : ∀ s ∈ Set.Ioo r r1, HasDerivAt h (h' s) s := by
    intro s hs
    have hs0 : s ∈ Set.Ioo 0 r1 := ⟨lt_trans hrpos hs.1, hs.2⟩
    exact hderiv s hs0
  have hQ' : ∀ s ∈ Set.Ioo r r1, Q = -2 * Real.pi * s * Tr * h' s := by
    intro s hs
    have hs0 : s ∈ Set.Ioo 0 r1 := ⟨lt_trans hrpos hs.1, hs.2⟩
    exact hQ s hs0
  have hr1mem : r1 ∈ Set.Icc r r1 := ⟨hrle, le_refl r1⟩
  have hmain := radialDarcy_head_sub hrpos hTr hcont' hderiv' hQ' r1 hr1mem
  have hratio : r1 / r = Real.exp K := by
    rw [hrdef]
    have h1 : r1 / (r1 * Real.exp (-K)) = 1 / Real.exp (-K) := by field_simp
    rw [h1, Real.exp_neg, one_div, inv_inv]
  have hlog : Real.log (r1 / r) = K := by
    rw [hratio, Real.log_exp]
  rw [hlog] at hmain
  have habs : |h r1 - h r| = 2 * M + 1 := by
    rw [hmain]
    have h1 : |-Q * K / (2 * Real.pi * Tr)| = |Q| * K / (2 * Real.pi * Tr) := by
      rw [abs_div, abs_mul, abs_neg]
      have hk : |K| = K := abs_of_pos hKpos
      have hden : |2 * Real.pi * Tr| = 2 * Real.pi * Tr := abs_of_pos hden_pos
      rw [hk, hden]
    rw [h1, hKdef]
    field_simp
  have hmem1 : r1 ∈ Set.Icc 0 r1 := ⟨le_of_lt hr1, le_refl r1⟩
  have hmemr : r ∈ Set.Icc 0 r1 := ⟨hr0le, hrle⟩
  have hb1 : |h r1| ≤ M := hMabs r1 hmem1
  have hbr : |h r| ≤ M := hMabs r hmemr
  have hle := abs_sub_le (h r1) 0 (h r)
  simp only [sub_zero, zero_sub, abs_neg] at hle
  have htri : |h r1 - h r| ≤ 2 * M := by linarith
  linarith

/-- A negative transmissivity is rejected: for `Tr < 0`, at a radius `r > 0` where the head
gradient `h'` is nonzero, the discharge `-2 π r Tr h'` has the sign of `h'`, so the water
would flow toward higher head. -/
lemma radialDischarge_upgradient_of_neg {Tr r h' : ℝ} (hTr : Tr < 0) (hr : 0 < r)
    (hh' : h' ≠ 0) :
    0 < (-2 * Real.pi * r * Tr * h') * h' := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < h' ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hh'
  have hTr' : 0 < -Tr := by linarith
  have h : (-2 * Real.pi * r * Tr * h') * h' = (2 * Real.pi * r * (-Tr)) * (h' ^ 2) := by ring
  rw [h]
  have hpos : 0 < 2 * Real.pi * r * (-Tr) := by positivity
  positivity

end EarthScience
