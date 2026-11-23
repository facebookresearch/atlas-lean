/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Infinite-slope slab geometry

## i. Overview

For a plane-parallel slab on a slope of angle `beta`, with slip-plane
area `A` and vertical depth `z`, the slab volume is `A * z * cos beta`
(the normal thickness is `z * cos beta`). Resolving the slab weight per
unit slip-plane area gives the normal stress `gamma * z * cos beta ^ 2`
and the driving shear stress `gamma * z * sin beta * cos beta`, where
`gamma` is unit weight and `z` is vertical depth, not normal thickness.
The model assumes the translation-invariant side-face resultants of the
infinite slope cancel, so the basal traction balances the resolved
weight. Section B adds the Mohr–Coulomb resisting stress as a
supplied model input and the safety-ratio admission: on a genuine
slope the driving stress is positive, and resisting over driving
stress is at least one exactly when resisting stress dominates.
Section C adds pore-pressure monotonicity: on the contact domain
`0 ≤ u ≤ σn`, raising `u` cannot raise the safety ratio, strictly
exactly when `φ > 0`, and constantly at `φ = 0`.
No global stability criterion is stated.

## ii. Key results

- `EarthScience.infiniteSlopeSlabVolume`: slab volume.
- `EarthScience.infiniteSlopeNormalStress_eq`,
  `EarthScience.infiniteSlopeDrivingStress_eq`: weight components per
  unit area are the two stresses.
- `EarthScience.infiniteSlopeDriving_eq_normal_mul_tan`: driving stress
  is normal stress times `tan beta` on a genuine slope.
- `EarthScience.infiniteSlopeSafetyRatio_admission`: the safety
  ratio is at least one iff resisting stress dominates driving
  stress.
- `EarthScience.effectiveNormalStress_eq`: the slip-plane normal
  component of effective stress is total normal stress minus `u`.
- `EarthScience.infiniteSlopeSafetyRatio_porePressure_monotonicity`
  and `infiniteSlopeSafetyRatio_antitoneOn_porePressure`: the
  safety ratio is antitone in pore pressure on `[0, σn]`,
  strictly exactly for positive friction.

## iii. Table of contents

- A. Slab volume and resolved stresses
- B. Safety-ratio admission
- C. Pore-pressure monotonicity

## iv. References

- B. M. Das and K. Sobhan, *Principles of Geotechnical Engineering*,
  10th edition, Cengage, 2022 (infinite slope without seepage).
- R. F. Craig, *Craig's Soil Mechanics*, 8th edition, CRC Press, 2012
  (infinite slopes).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Slab volume and resolved stresses -/

/-- Volume of a plane-parallel infinite-slope slab per slip-plane area `A`,
for vertical depth `z` and slope angle `beta` in radians:
`A * z * cos beta`. The thickness normal to the slip plane is
`z * cos beta`. -/
noncomputable def infiniteSlopeSlabVolume (A z beta : ℝ) : ℝ :=
  A * z * Real.cos beta

/-- Normal stress on the slip plane from the slab weight:
`gamma * z * cos beta ^ 2`, where `gamma` is unit weight and
`z` is vertical depth (not normal thickness). -/
noncomputable def infiniteSlopeNormalStress (gamma z beta : ℝ) : ℝ :=
  gamma * z * Real.cos beta ^ 2

/-- Driving shear stress on the slip plane from the slab weight:
`gamma * z * sin beta * cos beta`, with `z` vertical depth. -/
noncomputable def infiniteSlopeDrivingStress (gamma z beta : ℝ) : ℝ :=
  gamma * z * Real.sin beta * Real.cos beta

/-- The normal component of slab weight per slip-plane area `A > 0` is the
normal stress. -/
theorem infiniteSlopeNormalStress_eq {A gamma z beta : ℝ} (hA : 0 < A) :
    gamma * infiniteSlopeSlabVolume A z beta * Real.cos beta / A
      = infiniteSlopeNormalStress gamma z beta := by
  have hA0 : A ≠ 0 := hA.ne'
  unfold infiniteSlopeSlabVolume infiniteSlopeNormalStress
  field_simp

/-- The downslope component of slab weight per slip-plane area `A > 0` is the
driving shear stress. -/
theorem infiniteSlopeDrivingStress_eq {A gamma z beta : ℝ} (hA : 0 < A) :
    gamma * infiniteSlopeSlabVolume A z beta * Real.sin beta / A
      = infiniteSlopeDrivingStress gamma z beta := by
  have hA0 : A ≠ 0 := hA.ne'
  unfold infiniteSlopeSlabVolume infiniteSlopeDrivingStress
  field_simp

/-- On a genuine slope, driving stress is normal stress times `tan beta`. -/
theorem infiniteSlopeDriving_eq_normal_mul_tan {gamma z beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta : beta < Real.pi / 2) :
    infiniteSlopeDrivingStress gamma z beta
      = infiniteSlopeNormalStress gamma z beta * Real.tan beta := by
  have hcos : Real.cos beta ≠ 0 := by
    have hmem : beta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · have hpi : 0 < Real.pi := Real.pi_pos
        linarith
      · exact hbeta
    exact (Real.cos_pos_of_mem_Ioo hmem).ne'
  unfold infiniteSlopeDrivingStress infiniteSlopeNormalStress
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-! ## B. Safety-ratio admission -/

open scoped Matrix

/-- Mohr–Coulomb resisting shear stress on the slip plane
(supplied model input): effective cohesion `c` plus the
compression-positive effective normal stress `σn - u` (Biot
coefficient one, slip-plane pore pressure `u`) times
`tan phi`, for friction angle `phi`. `Real.tan` and the safety
ratio below use totalized real division; the admission theorems
assume a genuine slope, where the driving stress is positive.
With the convention `x / 0 = 0`, `tan phi = 0` where `cos phi = 0`,
so the resisting stress is then `c`. -/
noncomputable def infiniteSlopeResistingStress (c phi gamma z beta u : ℝ) :
    ℝ :=
  c + (infiniteSlopeNormalStress gamma z beta - u) * Real.tan phi

/-- Safety ratio `tauR / tau_d` of a resisting shear stress
against the slab driving stress (totalized division: with the
convention `x / 0 = 0`, it is `0` when `tau_d = 0`). -/
noncomputable def infiniteSlopeSafetyRatio (tauR gamma z beta : ℝ) : ℝ :=
  tauR / infiniteSlopeDrivingStress gamma z beta

/-- Denominator sign: the driving stress is positive on a
genuine slope (`0 < gamma`, `0 < z`, `0 < beta < π / 2`). -/
theorem infiniteSlopeDrivingStress_pos {gamma z beta : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2) :
    0 < infiniteSlopeDrivingStress gamma z beta := by
  unfold infiniteSlopeDrivingStress
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 0 < Real.sin beta :=
    Real.sin_pos_of_pos_of_lt_pi hbeta0 (by linarith)
  have hcos : 0 < Real.cos beta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hbeta⟩
  exact mul_pos (mul_pos (mul_pos hgamma hz) hsin) hcos

/-- Main result: on a genuine slope (`0 < gamma`, `0 < z`,
`0 < beta < π / 2`), `tau_d > 0`, and
`tauR / tau_d ≥ 1 ↔ tauR ≥ tau_d`. -/
theorem infiniteSlopeSafetyRatio_admission {tauR gamma z beta : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2) :
    0 < infiniteSlopeDrivingStress gamma z beta ∧
      (1 ≤ infiniteSlopeSafetyRatio tauR gamma z beta ↔
        infiniteSlopeDrivingStress gamma z beta ≤ tauR) := by
  have hpos : 0 < infiniteSlopeDrivingStress gamma z beta :=
    infiniteSlopeDrivingStress_pos hgamma hz hbeta0 hbeta
  refine ⟨hpos, ?_⟩
  unfold infiniteSlopeSafetyRatio
  exact one_le_div₀ hpos

/-- The admission for the Mohr–Coulomb resisting stress: on a genuine slope (`0 < gamma`, `0 < z`,
`0 < beta < π / 2`), the safety ratio is at least one exactly when the resisting stress is at least
the driving stress. Here `tan phi = 0` where `cos phi = 0`, by the convention `x / 0 = 0`. -/
theorem infiniteSlope_mohrCoulomb_admission {c phi gamma z beta u : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2) :
    1 ≤ infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta u) gamma z beta ↔
      infiniteSlopeDrivingStress gamma z beta
        ≤ infiniteSlopeResistingStress c phi gamma z beta u := by
  exact (infiniteSlopeSafetyRatio_admission hgamma hz hbeta0 hbeta).2

/-- On a unit normal `v`, the normal component of the
compression-positive effective stress is the total normal
component minus `u`. -/
theorem effectiveNormalStress_eq {m : ℕ} (σc : Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (v : Fin m → ℝ) (hv : v ⬝ᵥ v = 1) :
    v ⬝ᵥ (effectiveStressCompressionPositive σc u *ᵥ v)
      = v ⬝ᵥ (σc *ᵥ v) - u := by
  unfold effectiveStressCompressionPositive
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, hv, smul_eq_mul, mul_one]

/-! ## C. Pore-pressure monotonicity -/

/-- Two safety ratios differ by the change in effective normal stress times `tan phi` over the
driving stress: `F u₁ - F u₂ = (u₂ - u₁) * tan phi / τd`. An algebraic identity for all real inputs,
including `τd = 0` or `cos phi = 0`, with the convention `x / 0 = 0` on both sides; not a
monotonicity claim. -/
lemma infiniteSlopeSafetyRatio_porePressure_sub
    (c phi gamma z beta u₁ u₂ : ℝ) :
    infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta u₁)
        gamma z beta
      - infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta u₂)
        gamma z beta
      = (u₂ - u₁) * Real.tan phi
        / infiniteSlopeDrivingStress gamma z beta := by
  unfold infiniteSlopeSafetyRatio infiniteSlopeResistingStress
  ring

/-- Raising the pore pressure within the contact domain
`0 ≤ u ≤ σn` cannot raise the safety ratio of a slab on a
genuine slope (`0 < gamma`, `0 < z`, `0 < beta < π / 2`) with
`0 ≤ phi < π / 2`. Nothing is claimed for
`u > σn` (tensile effective stress; no tension cutoff) or
`u < 0` (suction). The cohesion `c` is unrestricted (it
cancels in the difference; physically `c ≥ 0`). The premises
give `tan phi ≥ 0` and `τd > 0`; for `π / 2 < phi < π`, where
`tan phi < 0`, the ratio increases with `u`. -/
theorem infiniteSlopeSafetyRatio_antitoneOn_porePressure
    {c phi gamma z beta : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2)
    (hphi0 : 0 ≤ phi) (hphi : phi < Real.pi / 2) :
    AntitoneOn
        (fun u => infiniteSlopeSafetyRatio
          (infiniteSlopeResistingStress c phi gamma z beta u)
          gamma z beta)
        (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta)) := by
  intro x _ y _ hxy
  have hτd : 0 < infiniteSlopeDrivingStress gamma z beta :=
    infiniteSlopeDrivingStress_pos hgamma hz hbeta0 hbeta
  have htan : 0 ≤ Real.tan phi :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hphi0 (le_of_lt hphi)
  have hdiff := infiniteSlopeSafetyRatio_porePressure_sub
    c phi gamma z beta y x
  have hle : (x - y) * Real.tan phi
      / infiniteSlopeDrivingStress gamma z beta ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxy) htan)
      (le_of_lt hτd)
  have hle' : infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta y)
        gamma z beta
      - infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta x)
        gamma z beta ≤ 0 := by
    rw [hdiff]
    exact hle
  exact sub_nonpos.mp hle'

/-- With positive friction `0 < phi < π / 2`, on a genuine slope
(`0 < gamma`, `0 < z`, `0 < beta < π / 2`), the decrease is
strict: for `0 ≤ u₁ < u₂ ≤ σn` the ratio at `u₂` is strictly
below the ratio at `u₁`. -/
theorem infiniteSlopeSafetyRatio_strictAntiOn_porePressure
    {c phi gamma z beta : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2)
    (hphi0 : 0 < phi) (hphi : phi < Real.pi / 2) :
    StrictAntiOn
        (fun u => infiniteSlopeSafetyRatio
          (infiniteSlopeResistingStress c phi gamma z beta u)
          gamma z beta)
        (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta)) := by
  intro x _ y _ hxy
  have hτd : 0 < infiniteSlopeDrivingStress gamma z beta :=
    infiniteSlopeDrivingStress_pos hgamma hz hbeta0 hbeta
  have htan : 0 < Real.tan phi :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hphi0 hphi
  have hdiff := infiniteSlopeSafetyRatio_porePressure_sub
    c phi gamma z beta y x
  have hlt : (x - y) * Real.tan phi
      / infiniteSlopeDrivingStress gamma z beta < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr hxy) htan) hτd
  have hlt' : infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta y)
        gamma z beta
      - infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta x)
        gamma z beta < 0 := by
    rw [hdiff]
    exact hlt
  exact sub_neg.mp hlt'

/-- Without friction the pore pressure drops out: at `phi = 0` the ratio is `c / τd` on the whole
contact domain, for all data, by `tan 0 = 0` (`c / τd` is the genuine ratio only on a genuine slope,
where `τd > 0`). Where `τd = 0` both sides are `0`, by the convention `x / 0 = 0`. -/
lemma infiniteSlopeSafetyRatio_eqOn_porePressure_of_phi_eq_zero
    {c gamma z beta : ℝ} :
    Set.EqOn
        (fun u => infiniteSlopeSafetyRatio
          (infiniteSlopeResistingStress c 0 gamma z beta u)
          gamma z beta)
        (fun _ => c / infiniteSlopeDrivingStress gamma z beta)
        (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta)) := by
  intro u _
  change infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress c 0 gamma z beta u)
      gamma z beta
    = c / infiniteSlopeDrivingStress gamma z beta
  unfold infiniteSlopeSafetyRatio infiniteSlopeResistingStress
  simp [Real.tan_zero]

/-- Main result: for a slab on a genuine slope (`0 < gamma`,
`0 < z`, `0 < beta < π / 2`) and
`0 ≤ phi < π / 2`, the safety ratio is antitone in the pore
pressure on `[0, σn]`, strictly antitone there exactly when
`0 < phi`, and constant (`c / τd`) there when `phi = 0`. The
premise `_hc` marks the admission domain (physically
nonnegative effective cohesion) and is not used by the
proof. No global stability or safety certification is
claimed. -/
theorem infiniteSlopeSafetyRatio_porePressure_monotonicity
    {c phi gamma z beta : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2)
    (hphi0 : 0 ≤ phi) (hphi : phi < Real.pi / 2) (_hc : 0 ≤ c) :
    AntitoneOn
        (fun u => infiniteSlopeSafetyRatio
          (infiniteSlopeResistingStress c phi gamma z beta u)
          gamma z beta)
        (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta)) ∧
      (StrictAntiOn
          (fun u => infiniteSlopeSafetyRatio
            (infiniteSlopeResistingStress c phi gamma z beta u)
            gamma z beta)
          (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta))
        ↔ 0 < phi) ∧
      (phi = 0 → Set.EqOn
          (fun u => infiniteSlopeSafetyRatio
            (infiniteSlopeResistingStress c phi gamma z beta u)
            gamma z beta)
          (fun _ => c / infiniteSlopeDrivingStress gamma z beta)
          (Set.Icc 0 (infiniteSlopeNormalStress gamma z beta))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteSlopeSafetyRatio_antitoneOn_porePressure
      hgamma hz hbeta0 hbeta hphi0 hphi
  · constructor
    · intro hstrict
      refine not_le.mp ?_
      intro hle
      have hphi0' : phi = 0 := le_antisymm hle hphi0
      have hcos : 0 < Real.cos beta := by
        apply Real.cos_pos_of_mem_Ioo
        refine ⟨?_, hbeta⟩
        have hpi := Real.pi_pos
        linarith
      have hsign : 0 < infiniteSlopeNormalStress gamma z beta := by
        unfold infiniteSlopeNormalStress
        exact mul_pos (mul_pos hgamma hz) (pow_pos hcos 2)
      have h0mem : (0 : ℝ) ∈
          Set.Icc 0 (infiniteSlopeNormalStress gamma z beta) :=
        ⟨le_rfl, le_of_lt hsign⟩
      have hσmem : infiniteSlopeNormalStress gamma z beta ∈
          Set.Icc 0 (infiniteSlopeNormalStress gamma z beta) :=
        ⟨le_of_lt hsign, le_rfl⟩
      subst hphi0'
      have hlt := hstrict h0mem hσmem hsign
      have heq :=
        infiniteSlopeSafetyRatio_eqOn_porePressure_of_phi_eq_zero
          (c := c) (gamma := gamma) (z := z) (beta := beta)
      have e0 := heq h0mem
      have eσ := heq hσmem
      rw [eσ, e0] at hlt
      exact lt_irrefl _ hlt
    · intro hpos
      exact infiniteSlopeSafetyRatio_strictAntiOn_porePressure
        hgamma hz hbeta0 hbeta hpos hphi
  · intro h
    subst h
    exact infiniteSlopeSafetyRatio_eqOn_porePressure_of_phi_eq_zero

end EarthScience
