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

## iii. Table of contents

- A. Slab volume and resolved stresses
- B. Safety-ratio admission

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

/-- The normal component of slab weight per slip-plane area is the
normal stress. -/
theorem infiniteSlopeNormalStress_eq {A gamma z beta : ℝ} (hA : 0 < A) :
    gamma * infiniteSlopeSlabVolume A z beta * Real.cos beta / A
      = infiniteSlopeNormalStress gamma z beta := by
  have hA0 : A ≠ 0 := hA.ne'
  unfold infiniteSlopeSlabVolume infiniteSlopeNormalStress
  field_simp

/-- The downslope component of slab weight per slip-plane area is the
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
assume a genuine slope, where the driving stress is positive. -/
noncomputable def infiniteSlopeResistingStress (c phi gamma z beta u : ℝ) :
    ℝ :=
  c + (infiniteSlopeNormalStress gamma z beta - u) * Real.tan phi

/-- Safety ratio `tauR / tau_d` of a resisting shear stress
against the slab driving stress (totalized division). -/
noncomputable def infiniteSlopeSafetyRatio (tauR gamma z beta : ℝ) : ℝ :=
  tauR / infiniteSlopeDrivingStress gamma z beta

/-- Denominator sign: the driving stress is positive on a
genuine slope. -/
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

/-- Main result: `tau_d > 0`, and
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

/-- The admission for the Mohr–Coulomb resisting stress. -/
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

end EarthScience
