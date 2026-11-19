/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Reliability.PhysicalFailureEvents
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
stress yet a crack under it fails. Linear damage `d0 + r t` has the
lifetime `(D - d0) / r`, `⊤` without growth and `0` when initially
failed; at its lifetime the damage equals the threshold and the
component is down; two components sharing one damage path have equal
series and parallel lifetimes.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section C defines the von Mises
functional as an example of a supplied yield functional and checks that
it is calibrated by the tensile test. Section D proves the closed-form
lifetime of linear damage that its later examples use.

## iii. Table of contents

- A. Unit-parameter threshold
- B. Degenerate stress
- C. Demand margins, the axial bar and the hydrostatic boundary
- D. Damage hitting times and monotone systems

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

/-! ## D. Damage hitting times and monotone systems -/

open MeasureTheory
open scoped NNReal ENNReal

variable {Ω : Type*}

/-- Linear damage `d0 + r t` with `r > 0` below threshold at time zero (`d0 < D`) fails at
`(D - d0) / r`; for example `d0 = 1`, `r = 2`, `D = 5` gives `2`. -/
lemma linearDamage_lifetime {d0 r D : ℝ} (hr : 0 < r) (hd : d0 < D) (ω : Ω) :
    damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω = ENNReal.ofReal ((D - d0) / r) := by
  have hcont : Continuous fun t : ℝ≥0 => d0 + r * (t : ℝ) :=
    continuous_const.add (continuous_const.mul NNReal.continuous_coe)
  have hmono : Monotone fun t : ℝ≥0 => d0 + r * (t : ℝ) := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := hab
    simp only
    nlinarith
  have hpos : 0 ≤ (D - d0) / r := div_nonneg (by linarith) hr.le
  have hcoe : (((D - d0) / r).toNNReal : ℝ) = (D - d0) / r := Real.coe_toNNReal _ hpos
  change damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω =
    ((((D - d0) / r).toNNReal : ℝ≥0) : ℝ≥0∞)
  apply le_antisymm
  · refine (damageLifetime_le_iff (d := fun _ t => d0 + r * t) (D := fun _ => D) (ω := ω)
      hcont hmono _).mpr ?_
    change D ≤ d0 + r * (((D - d0) / r).toNNReal : ℝ)
    rw [hcoe]
    field_simp
    linarith
  · refine ENNReal.le_of_forall_nnreal_lt fun s hs => le_of_lt ?_
    refine (lt_damageLifetime_iff (d := fun _ t => d0 + r * t) (D := fun _ => D) (ω := ω)
      hcont hmono s).mpr ?_
    have hs' : (s : ℝ) < (D - d0) / r := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hcoe] at hs
      exact hs
    change d0 + r * (s : ℝ) < D
    rw [lt_div_iff₀ hr] at hs'
    linarith

/-- Linear damage `1 + 2 t` against the threshold `5` fails at `t = 2`. -/
example (ω : Ω) : damageLifetime (fun _ t => 1 + 2 * t) (fun _ => 5) ω = 2 := by
  rw [linearDamage_lifetime (by norm_num) (by norm_num) ω]
  norm_num

/-- Linear damage with zero rate below threshold never fails: the lifetime is `⊤`. -/
example {d0 D : ℝ} (hd : d0 < D) (ω : Ω) :
    damageLifetime (fun _ t => d0 + 0 * t) (fun _ => D) ω = ⊤ := by
  rw [damageLifetime_eq_top_iff]
  intro t
  simp only [zero_mul, add_zero]
  exact hd

/-- Initially failed linear damage (`D ≤ d0`) has lifetime `0`, not `⊤`, for every rate. -/
example {d0 D : ℝ} (hd : D ≤ d0) (r : ℝ) (ω : Ω) :
    damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω = 0 ∧
      damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω ≠ ⊤ := by
  have h0 : damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω = 0 :=
    damageLifetime_eq_zero (by simp only [NNReal.coe_zero, mul_zero, add_zero]; exact hd)
  exact ⟨h0, by rw [h0]; exact ENNReal.zero_ne_top⟩

/-- Equality at the threshold is failure: at its lifetime `(D - d0) / r` the linear damage
equals the threshold, the demand event holds, and the component is no longer up. -/
example {d0 r D : ℝ} (hr : 0 < r) (hd : d0 < D) (ω : Ω) :
    d0 + r * ((D - d0) / r).toNNReal = D ∧
      demandFailure D (d0 + r * ((D - d0) / r).toNNReal) ∧
      ¬ (((D - d0) / r).toNNReal : ℝ≥0∞) <
        damageLifetime (fun _ t => d0 + r * t) (fun _ => D) ω := by
  have hpos : 0 ≤ (D - d0) / r := div_nonneg (by linarith) hr.le
  have hcoe : (((D - d0) / r).toNNReal : ℝ) = (D - d0) / r := Real.coe_toNNReal _ hpos
  have heq : d0 + r * (((D - d0) / r).toNNReal : ℝ) = D := by
    rw [hcoe]
    field_simp
    ring
  refine ⟨heq, ?_, ?_⟩
  · change D ≤ d0 + r * (((D - d0) / r).toNNReal : ℝ)
    rw [heq]
  · rw [linearDamage_lifetime hr hd ω]
    exact lt_irrefl _

/-- Dependent components stay dependent: two components sharing one damage path and threshold
have equal series and parallel lifetimes, both the common lifetime; no product formula holds. -/
example (d : Ω → ℝ≥0 → ℝ) (D : Ω → ℝ) (ω : Ω) :
    systemLifetime (Fin 2) (seriesEvent (Fin 2)) (fun _ => damageLifetime d D ω) =
        damageLifetime d D ω ∧
      systemLifetime (Fin 2) (parallelEvent (Fin 2)) (fun _ => damageLifetime d D ω) =
        damageLifetime d D ω := by
  refine ⟨?_, ?_⟩
  · rw [systemLifetime_series]
    exact Finset.inf_const Finset.univ_nonempty _
  · rw [systemLifetime_parallel]
    exact Finset.sup_const Finset.univ_nonempty _

end PhyslibExtTest.Reliability.PhysicalFailureEvents
