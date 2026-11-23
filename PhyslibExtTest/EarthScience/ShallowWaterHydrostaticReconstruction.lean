/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shallow-water hydrostatic-reconstruction checks

Concrete consumers of
`PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction`: the
public shapes, the unequal-bed lake at rest `zL = 0`, `zR = 1`,
`η = 3` at `g = 2` (corrected fluxes `9` and `4`; mirror `4` and `9`),
its one-sided corrections, the dry-endpoint exclusion and contrast, and
negative controls with unequal free surfaces or nonzero discharge.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new public definitions or results are introduced here. The physical
fluxes below are private test fixtures.

## iii. Table of contents

- A. Public shapes
- B. Unequal beds and one-sided corrections
- C. Dry endpoint and negative controls

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction`
-/

open EarthScience.HydrostaticReconstruction

/-- The totalized physical flux of one conserved state, used only as a
test fixture. On a wet state `(h, h * u)` its second component is
`h * u ^ 2 + g * h ^ 2 / 2`; at `h = 0` Lean's division gives the
value used in the dry-endpoint contrast below. -/
private noncomputable def physicalFlux (g : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2)

/-- The left-state physical flux, consistent on wet states. -/
private noncomputable def leftPhysicalFlux (g : ℝ) : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun p _ => physicalFlux g p

/-- The right-state physical flux, consistent on wet states. -/
private noncomputable def rightPhysicalFlux (g : ℝ) : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun _ p => physicalFlux g p

/-- Wet-state consistency of the physical fixture flux. -/
private lemma physicalFlux_consistent {g h u : ℝ} (hh : 0 < h) :
    physicalFlux g (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2) := by
  have hne : h ≠ 0 := ne_of_gt hh
  have hdiv : (h * u) ^ 2 / h = h * u ^ 2 := by
    rw [div_eq_iff hne, mul_pow, mul_assoc, mul_comm (u ^ 2) h,
      ← mul_assoc, ← pow_two]
  show (h * u, (h * u) ^ 2 / h + g * h ^ 2 / 2) = _
  rw [hdiv]

/-- Wet-state consistency of the left-state fixture flux. -/
private lemma leftPhysicalFlux_consistent {g h u : ℝ} (hh : 0 < h) :
    leftPhysicalFlux g (h, h * u) (h, h * u) =
      (h * u, h * u ^ 2 + g * h ^ 2 / 2) :=
  physicalFlux_consistent hh

/-- Wet-state consistency of the right-state fixture flux. -/
private lemma rightPhysicalFlux_consistent {g h u : ℝ} (hh : 0 < h) :
    rightPhysicalFlux g (h, h * u) (h, h * u) =
      (h * u, h * u ^ 2 + g * h ^ 2 / 2) :=
  physicalFlux_consistent hh

/-! ## A. Public shapes -/

/-- The public statement shape of the reconstruction identity. -/
example {η hL uL hR uR zL zR : ℝ}
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    faceState hL uL zL (max zL zR) = (η - max zL zR, 0) ∧
      faceState hR uR zR (max zL zR) = (η - max zL zR, 0) :=
  faceState_eq_of_lake_at_rest hηL hηR hwet hqL hqR

/-- The public statement shape of wet-bed face balance. -/
example {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    (leftFlux g numFlux hL uL hR uR zL zR).2 = g * hL ^ 2 / 2 ∧
      (rightFlux g numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 :=
  hydrostatic_face_balance numFlux hcons hηL hηR hwet hqL hqR

/-- The public statement shape of the one-sided step control. -/
example {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hg : 0 < g) (hstep : zL < zR)
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    (interfaceFlux numFlux hL uL hR uR zL zR).2 < g * hL ^ 2 / 2 ∧
      (interfaceFlux numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 :=
  interfaceFlux_snd_of_step numFlux hcons hg hstep hηL hηR hwet hqL hqR

/-- The public statement shape of the dry-endpoint exclusion. -/
example (g zL zR : ℝ) (hstep : zL < zR) :
    ∃ numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ,
      (∀ h u : ℝ, 0 < h →
        numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2)) ∧
      (leftFlux g numFlux (zR - zL) 0 0 0 zL zR).2 ≠ g * (zR - zL) ^ 2 / 2 :=
  exists_dry_left_face_imbalance g zL zR hstep

/-! ## B. Unequal beds and one-sided corrections -/

/-- Unequal beds `zL = 0`, `zR = 1`, `η = 3`, `g = 2`: the corrected
momentum fluxes are `9` on the left and `4` on the right. -/
example :
    (leftFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 9 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 4 := by
  have h : (leftFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 2 * 3 ^ 2 / 2 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 2 * 2 ^ 2 / 2 :=
    hydrostatic_face_balance (η := 3) (leftPhysicalFlux 2)
      (fun h u hh => leftPhysicalFlux_consistent hh)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The mirror unequal-bed fixture: corrected fluxes `4` and `9`. -/
example :
    (leftFlux 2 (leftPhysicalFlux 2) 2 0 3 0 1 0).2 = 4 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 2 0 3 0 1 0).2 = 9 := by
  have h : (leftFlux 2 (leftPhysicalFlux 2) 2 0 3 0 1 0).2 = 2 * 2 ^ 2 / 2 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 2 0 3 0 1 0).2 = 2 * 3 ^ 2 / 2 :=
    hydrostatic_face_balance (η := 3) (leftPhysicalFlux 2)
      (fun h u hh => leftPhysicalFlux_consistent hh)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- One-sided corrections at the unequal-bed fixture: the uncorrected
interface momentum is `4 < 9`; the left correction is `5` and the
right correction is `0`. -/
example :
    (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 4 ∧
      (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 < 9 ∧
      (leftFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 -
          (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 5 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 -
          (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 0 := by
  have hstep : (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 <
        2 * 3 ^ 2 / 2 ∧
      (interfaceFlux (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 2 * 2 ^ 2 / 2 :=
    interfaceFlux_snd_of_step (η := 3) (leftPhysicalFlux 2)
      (fun h u hh => leftPhysicalFlux_consistent hh)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hbal : (leftFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 2 * 3 ^ 2 / 2 ∧
      (rightFlux 2 (leftPhysicalFlux 2) 3 0 2 0 0 1).2 = 2 * 2 ^ 2 / 2 :=
    hydrostatic_face_balance (η := 3) (leftPhysicalFlux 2)
      (fun h u hh => leftPhysicalFlux_consistent hh)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hstep hbal
  exact ⟨hstep.2, hstep.1, by linarith, by linarith⟩

/-! ## C. Dry endpoint and negative controls -/

/-- Dry endpoint exclusion at the concrete step `0 < 1`, `g = 2`. -/
example :
    ∃ numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ,
      (∀ h u : ℝ, 0 < h →
        numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + 2 * h ^ 2 / 2)) ∧
      (leftFlux 2 numFlux (1 - 0) 0 0 0 0 1).2 ≠ 2 * (1 - 0) ^ 2 / 2 :=
  exists_dry_left_face_imbalance 2 0 1 (by norm_num)

/-- Contrast at the dry endpoint: the totalized physical flux, which
is also consistent at the dry state `(0, 0)`, balances with value `1`. -/
example :
    (leftFlux 2 (leftPhysicalFlux 2) 1 0 0 0 0 1).2 = 1 := by
  norm_num [leftFlux, leftPhysicalFlux, physicalFlux, interfaceFlux,
    faceState, faceDepth]

/-- Negative control with unequal free surfaces: flat beds, depths
`2` and `3`, zero velocities. The right-state physical flux is wet
consistent, but no common `η` exists; the corrected left momentum is
`9`, not the left hydrostatic value `4`. -/
example :
    (leftFlux 2 (rightPhysicalFlux 2) 2 0 3 0 0 0).2 = 9 ∧
      (leftFlux 2 (rightPhysicalFlux 2) 2 0 3 0 0 0).2 ≠ 4 := by
  norm_num [leftFlux, rightPhysicalFlux, physicalFlux, interfaceFlux,
    faceState, faceDepth]

/-- Negative control with nonzero left discharge: at the unequal-bed
fixture with `uL = 1`, the corrected left momentum is `11`, not `9`. -/
example :
    (leftFlux 2 (leftPhysicalFlux 2) 3 1 2 0 0 1).2 = 11 ∧
      (leftFlux 2 (leftPhysicalFlux 2) 3 1 2 0 0 1).2 ≠ 9 := by
  norm_num [leftFlux, leftPhysicalFlux, physicalFlux, interfaceFlux,
    faceState, faceDepth]

#print axioms EarthScience.HydrostaticReconstruction.faceState_eq_of_lake_at_rest
#print axioms EarthScience.HydrostaticReconstruction.hydrostatic_face_balance
#print axioms EarthScience.HydrostaticReconstruction.interfaceFlux_snd_of_step
#print axioms EarthScience.HydrostaticReconstruction.exists_dry_left_face_imbalance
