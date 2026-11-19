/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Reliability.PhysicalFailureEvents
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Critical crack length checks

Concrete consumers of `PhyslibExt.Reliability.PhysicalFailureEvents`:
the critical length for unit geometry and stress, sharpness at the
threshold, the subcritical zero crack, and the degenerate zero-stress
case showing the positivity hypotheses cannot be dropped. A steel-like
fixed-fixed bar in newtons and millimetres has the end demand `100` MPa
for every calibrated yield functional, checked against allowables
below, at and above it; a hydrostatic tension has zero von Mises
stress yet a crack under it fails. A solid shaft under `M = 10⁶` N·mm
and `T = 2 × 10⁶` N·mm has the demand `512 / π` MPa at `d = 50` mm and
`1000 / π` MPa at `d = 40` mm for every functional calibrated on
bending-torsion states with `c = 3`, the von Mises functional among
them; the minimum diameter lies between, and a zero diameter or a stress
concentration at the minimum diameter is not covered.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section C defines the von Mises
functional as an example of a supplied yield functional and checks that
it is calibrated by the tensile test; section D checks that it is
calibrated on bending-torsion states with shear factor `3`.

## iii. Table of contents

- A. Unit-parameter threshold
- B. Degenerate stress
- C. Demand margins, the axial bar and the hydrostatic boundary
- D. A solid circular shaft under bending and torsion

## iv. References

- `PhyslibExt.Reliability.PhysicalFailureEvents`
-/

/-- Unit geometry and stress with toughness `2`: `a_c = 4 / π`. -/
example : Reliability.criticalCrackLength 2 1 1 = 4 / Real.pi := by
  unfold Reliability.criticalCrackLength
  norm_num

/-- The critical length for unit parameters is positive. -/
example : 0 < Reliability.criticalCrackLength 2 1 1 :=
  Reliability.criticalCrackLength_pos (by norm_num) one_pos one_pos

/-- At the critical length the intensity reaches the toughness `2`. -/
example :
    Reliability.modeIStressIntensity 1 1
        (Reliability.criticalCrackLength 2 1 1) = 2 :=
  Reliability.modeIStressIntensity_criticalCrackLength
    (by norm_num) one_pos one_pos

/-- Failure is equality-inclusive: the critical length itself fails. -/
example :
    Reliability.crackFailure 2 1 1 (Reliability.criticalCrackLength 2 1 1) :=
  (Reliability.crackFailure_iff_criticalCrackLength_le (by norm_num) one_pos
    one_pos (le_of_lt (Reliability.criticalCrackLength_pos
      (by norm_num) one_pos one_pos))).mpr le_rfl

/-- The zero crack is subcritical and does not fail. -/
example : Reliability.modeIStressIntensity 1 1 0 < 2 ∧
    ¬ Reliability.crackFailure 2 1 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [Reliability.modeIStressIntensity_zero]
    norm_num
  · rw [Reliability.crackFailure_iff_criticalCrackLength_le (by norm_num)
      one_pos one_pos le_rfl]
    exact not_le.mpr (Reliability.criticalCrackLength_pos
      (by norm_num) one_pos one_pos)

/-- Boundary degeneracy: with zero stress the adopted intensity is
identically zero, so the threshold characterization needs its positivity
hypotheses. -/
example (a : ℝ) : Reliability.modeIStressIntensity 1 0 a = 0 := by
  simp [Reliability.modeIStressIntensity]

/-- Paris power branch at `m = 3` (so `r = -1/2`), `K = 1`, `a0 = 1`:
the crack reaches `ac = 2` at its positive life, and the life precedes
the blow-up count `2`. -/
example : 0 < Reliability.parisLifePow (-1/2) 1 1 2 ∧
    Reliability.parisCrackPow (-1/2) 1 1
        (Reliability.parisLifePow (-1/2) 1 1 2) = 2 ∧
      Reliability.parisLifePow (-1/2) 1 1 2 <
        (1:ℝ) ^ (-1/2:ℝ) / (-((-1/2) * 1)) :=
  ⟨Reliability.parisLifePow_pos (by norm_num) one_pos (by norm_num)
      (by norm_num),
    Reliability.parisCrackPow_at_life (by norm_num) one_pos (by norm_num)
      (by norm_num),
    Reliability.parisLifePow_lt_blowup (by norm_num) one_pos (by norm_num)
      (by norm_num)⟩

/-- Paris logarithmic branch at `K = 1`, `a0 = 1`: the crack reaches
`ac = 2` at `log 2`. -/
example : Reliability.parisCrackExp 1 1 (Reliability.parisLifeExp 1 1 2) = 2 :=
  Reliability.parisCrackExp_at_life (by norm_num) one_pos (by norm_num)

/-- Paris derivative API at the negative-`r` point `N = 1`
(`r = -1/2`, `K = 1`, `a0 = 1`; base `1 - 1/2 = 1/2 > 0`). -/
example :
    HasDerivAt (Reliability.parisCrackPow (-1/2) 1 1)
      (1 * (Reliability.parisCrackPow (-1/2) 1 1 1) ^ ((1 - (-1/2 : ℝ)) : ℝ)) 1 :=
  Reliability.hasDerivAt_parisCrackPow (r := -1/2) (K := 1) (a0 := 1)
    (N := 1) (by norm_num)
    (by rw [Real.one_rpow]; norm_num)

/-- Paris logarithmic derivative API at `N = 0`. -/
example :
    HasDerivAt (Reliability.parisCrackExp 1 1)
      (1 * Reliability.parisCrackExp 1 1 0) 0 :=
  Reliability.hasDerivAt_parisCrackExp 1 1 0

/-- Power-branch first crossing at `N = 0`: crack `1` is below
`ac = 2`, using the positive life. -/
example : Reliability.parisCrackPow (-1/2) 1 1 0 < 2 :=
  (Reliability.parisCrackPow_lt_iff (r := -1/2) (K := 1) (a0 := 1)
    (ac := 2) (N := 0) (by norm_num) one_pos (by norm_num) (by norm_num)
    (by rw [Real.one_rpow]; norm_num)).mpr
    (Reliability.parisLifePow_pos (r := -1/2) (K := 1) (a0 := 1) (ac := 2)
      (by norm_num) one_pos (by norm_num) (by norm_num))

/-- Log-branch first crossing at `N = 0`. -/
example : Reliability.parisCrackExp 1 1 0 < 2 :=
  (Reliability.parisCrackExp_lt_iff (K := 1) (a0 := 1) (ac := 2) (N := 0)
    (by norm_num) one_pos (by norm_num)).mpr
    (Reliability.parisLifeExp_pos (K := 1) (a0 := 1) (ac := 2)
      (by norm_num) one_pos (by norm_num))

/-! ## C. Demand margins, the axial bar and the hydrostatic boundary -/

@[expose] public section

namespace PhyslibExtTest.Reliability.PhysicalFailureEvents

open _root_.Reliability

/-- A steel-like bar in newtons and millimetres: `EA = 2 × 10⁸`, `L = 2000`, `q = 100`,
`A_cs = 1000`. The end-section demand is `100` (MPa) for every calibrated functional. -/
example {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} (hΦ : UniaxialCalibrated Φ) :
    Φ (Matrix.diagonal ![axialStress 200000000 2000 100 1000 0, 0, 0]) = 100 := by
  rw [axialDemand_eq hΦ (by norm_num) (by norm_num)]
  norm_num

/-- The demand `100` against allowables below, at and above it: `250` (no failure, margin `150`,
margin of safety `3 / 2`), `100` (failure at equality, both margins `0`) and `80` (failure,
margin `-20`, margin of safety `-1 / 5`). -/
example :
    (¬ demandFailure 250 100 ∧ dimensionalMargin 250 100 = 150 ∧
        marginOfSafety 250 100 (by norm_num) = 3 / 2) ∧
      (demandFailure 100 100 ∧ dimensionalMargin 100 100 = 0 ∧
        marginOfSafety 100 100 (by norm_num) = 0) ∧
      (demandFailure 80 100 ∧ dimensionalMargin 80 100 = -20 ∧
        marginOfSafety 80 100 (by norm_num) = -1 / 5) := by
  simp only [demandFailure, dimensionalMargin, marginOfSafety]
  norm_num

/-- The von Mises equivalent stress
`√(((σ₁₁ - σ₂₂)² + (σ₂₂ - σ₃₃)² + (σ₃₃ - σ₁₁)²) / 2 + 3 (σ₁₂² + σ₂₃² + σ₃₁²))`, read on the
diagonal and the upper shear components: a fixture example of a supplied yield functional. -/
noncomputable def vonMisesStress (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (((σ 0 0 - σ 1 1) ^ 2 + (σ 1 1 - σ 2 2) ^ 2 + (σ 2 2 - σ 0 0) ^ 2) / 2 +
    3 * (σ 0 1 ^ 2 + σ 1 2 ^ 2 + σ 0 2 ^ 2))

/-- The von Mises functional is calibrated by the tensile test, so calibrated functionals
exist. -/
lemma vonMisesStress_uniaxialCalibrated : UniaxialCalibrated vonMisesStress := by
  intro σ
  simp only [vonMisesStress, Matrix.diagonal_apply]
  simp
  exact Real.sqrt_sq_eq_abs σ

/-- The hydrostatic tension `100 • 1` has zero von Mises stress but is not the zero stress; the
yield event against the allowable `250` does not occur, while a crack of length `1 / 100` with
`Y = 1` under the same tension fails against the toughness `5`. -/
example :
    vonMisesStress ((100 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 ∧
      (100 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 ∧
      ¬ demandFailure 250 (vonMisesStress ((100 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))) ∧
      crackFailure 5 1 100 (1 / 100) := by
  have hvm : vonMisesStress ((100 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
    simp [vonMisesStress]
  refine ⟨hvm, ?_, ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · rw [hvm]
    unfold demandFailure
    norm_num
  · unfold crackFailure modeIStressIntensity
    have hs : (1 / 20 : ℝ) ≤ Real.sqrt (Real.pi * (1 / 100)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.two_le_pi]
    nlinarith

/-- With the von Mises functional the fixture bar fails at the allowable `100` (equality at the
ends) and nowhere at `250`. -/
example :
    (∃ x ∈ Set.Icc (0 : ℝ) 2000, demandFailure 100
        (vonMisesStress (Matrix.diagonal ![axialStress 200000000 2000 100 1000 x, 0, 0]))) ∧
      ¬ ∃ x ∈ Set.Icc (0 : ℝ) 2000, demandFailure 250
        (vonMisesStress (Matrix.diagonal ![axialStress 200000000 2000 100 1000 x, 0, 0])) := by
  refine ⟨(axialBar_failure_iff vonMisesStress_uniaxialCalibrated (by norm_num) (by norm_num)
    (by norm_num) 100 100).2 (by norm_num), fun h => ?_⟩
  have h' := (axialBar_failure_iff vonMisesStress_uniaxialCalibrated (by norm_num) (by norm_num)
    (by norm_num) 100 250).1 h
  norm_num at h'

/-! ## D. A solid circular shaft under bending and torsion -/

/-- The von Mises functional is calibrated on bending-torsion states with shear factor `3`, so
calibrated functionals exist. -/
lemma vonMisesStress_bendingTorsionCalibrated :
    BendingTorsionCalibrated PhyslibExtTest.Reliability.PhysicalFailureEvents.vonMisesStress 3 := by
  intro σ τ
  simp only [PhyslibExtTest.Reliability.PhysicalFailureEvents.vonMisesStress, bendingTorsionState]
  simp

-- The bending-torsion calibration of the von Mises functional contains its tensile calibration.
example : UniaxialCalibrated vonMisesStress :=
  vonMisesStress_bendingTorsionCalibrated.uniaxialCalibrated

-- Nonzero combined loading in newtons and millimetres: `M = 10⁶` N·mm and `T = 2 × 10⁶` N·mm
-- with `c = 3` against the allowable `250` MPa. Then `4 M ^ 2 + 3 T ^ 2 = (4 × 10⁶) ^ 2`; the
-- demand is `512 / π ≈ 163` MPa at `d = 50` mm (no failure) and `1000 / π ≈ 318` MPa at
-- `d = 40` mm (failure); the minimum diameter is `(256000 / π) ^ (1 / 3) ≈ 43.4` mm. 
example {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ}
    (hΦ : BendingTorsionCalibrated Φ 3) :
    Φ (bendingTorsionState (shaftBendingStress 1000000 50) (shaftShearStress 2000000 50)) =
        512 / Real.pi ∧
      ¬ Reliability.demandFailure 250
        (Φ (bendingTorsionState (shaftBendingStress 1000000 50) (shaftShearStress 2000000 50))) ∧
      Φ (bendingTorsionState (shaftBendingStress 1000000 40) (shaftShearStress 2000000 40)) =
        1000 / Real.pi ∧
      Reliability.demandFailure 250
        (Φ (bendingTorsionState (shaftBendingStress 1000000 40) (shaftShearStress 2000000 40))) ∧
      shaftMinDiameter 3 1000000 2000000 250 ^ 3 = 256000 / Real.pi := by
  have h50 := shaftDemand_eq hΦ (by norm_num : (0 : ℝ) < 50) 1000000 2000000
  have h40 := shaftDemand_eq hΦ (by norm_num : (0 : ℝ) < 40) 1000000 2000000
  have hs : Real.sqrt (4 * 1000000 ^ 2 + 3 * 2000000 ^ 2) = 4000000 := by
    rw [show (4 * 1000000 ^ 2 + 3 * 2000000 ^ 2 : ℝ) = 4000000 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs] at h50 h40
  have hπ : 0 < Real.pi := Real.pi_pos
  have h3 : 3 < Real.pi := Real.pi_gt_three
  have h4 : Real.pi < 4 := Real.pi_lt_four
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h50]
    field_simp
    ring
  · rw [h50]
    unfold Reliability.demandFailure
    rw [not_le, div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [h40]
    field_simp
    ring
  · rw [h40]
    unfold Reliability.demandFailure
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · unfold shaftMinDiameter
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    field_simp
    ring

-- With these loads the minimum diameter is positive and below `50` mm for every functional
-- calibrated with `c = 3`.
example {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} (hΦ : BendingTorsionCalibrated Φ 3) :
    0 < shaftMinDiameter 3 1000000 2000000 250 ∧ shaftMinDiameter 3 1000000 2000000 250 < 50 := by
  refine ⟨shaftMinDiameter_pos (by norm_num) (by norm_num) (Or.inl (by norm_num)), ?_⟩
  refine (not_demandFailure_iff hΦ (by norm_num) (by norm_num) 1000000 2000000).1 ?_
  rw [shaftDemand_eq hΦ (by norm_num),
    show (4 * 1000000 ^ 2 + 3 * 2000000 ^ 2 : ℝ) = 4000000 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  unfold demandFailure
  rw [not_le, div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

-- The zero diameter misreports with the von Mises functional too: zero demand, no failure.
example :
    ¬ demandFailure 250 (vonMisesStress (bendingTorsionState (shaftBendingStress 1000000 0)
      (shaftShearStress 2000000 0))) :=
  (zero_diameter_misreports vonMisesStress_bendingTorsionCalibrated (by norm_num) 1000000
    2000000).2

-- At the minimum diameter for these loads a bending stress-concentration factor `2` raises the
-- von Mises demand above the allowable `250`.
example :
    250 < vonMisesStress (bendingTorsionState
      (2 * shaftBendingStress 1000000 (shaftMinDiameter 3 1000000 2000000 250))
      (shaftShearStress 2000000 (shaftMinDiameter 3 1000000 2000000 250))) :=
  (stressConcentration_exceeds_at_minDiameter vonMisesStress_bendingTorsionCalibrated
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2000000).2

end PhyslibExtTest.Reliability.PhysicalFailureEvents
