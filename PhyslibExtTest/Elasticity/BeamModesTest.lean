/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.BeamModes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue

/-!
# Beam mode checks

Concrete consumers of `PhyslibExt.Elasticity.BeamModes`: the first
mode `k = 1` on a beam with `L = 2`, `EI = 3`, `ρA = 1`, its support
values, and its conserved energy; the first clamped-free mode on the
same beam, a certified bracket `(1.875, 1.876)` around its root,
the characteristic equation at that root and at `β L = π / 2`, the
`1 / L ^ 2` frequency scaling, and the failure of the old root bracket.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

- `PhyslibExtTest.Elasticity.BeamModes.cantileverRoot_bracket`: the
  certified bracket `1.875 < z₁ < 1.876`, a numerical illustration.

## iii. Table of contents

- A. First mode on a concrete beam
- B. The clamped-free mode

## iv. References

- `PhyslibExt.Elasticity.BeamModes`
-/

/-- Support values and conserved energy of the first mode at
`L = 2`, `EI = 3`, `ρA = 1`, at arbitrary time `t`. -/
example (t : ℝ) :
    BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 0 t = 0 ∧
      BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 2 t = 0 ∧
        BeamModes.beamModeEnergy 3 1 2 (BeamModes.beamFreq 3 1 2 1) 1 t =
          (2 / 4) * 3 * ((1 : ℝ) * Real.pi / 2) ^ 4 :=
  ⟨BeamModes.beamMode_zero_left 1 2 _ t,
   BeamModes.beamMode_zero_right 1 (by norm_num) _ t,
   (by
     have h := BeamModes.beamModeEnergy_conserved (EI := 3) (ρA := 1)
       (L := 2) (by norm_num) (by norm_num) (by norm_num) 1 t
     simpa using h)⟩

/-- The beam equation and curvature conditions for the first mode at
`L = 2`, `EI = 3`, `ρA = 1`, at the interior point `x = 1`,
`t = 0`. -/
example : (1 : ℝ) * iteratedDeriv 2
      (fun s : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 1 s) 0 +
    3 * iteratedDeriv 4
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 1 =
    0 ∧
  iteratedDeriv 2
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 0 =
    0 ∧
  iteratedDeriv 2
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 2 =
    0 :=
  ⟨BeamModes.beamMode_beamEquation (by norm_num) (by norm_num)
    (by norm_num) 1 1 0,
   (BeamModes.beamMode_curvature_zero 1 (by norm_num) _ 0).1,
   (BeamModes.beamMode_curvature_zero 1 (by norm_num) _ 0).2⟩

/-! ## B. The clamped-free mode -/

@[expose] public section

namespace PhyslibExtTest.Elasticity.BeamModes

open _root_.BeamModes

/-- Bounds on `exp 0.9375` from the degree-7 Taylor bound. -/
private lemma exp_bounds_15_16 : 2.55355 ≤ Real.exp 0.9375 ∧ Real.exp 0.9375 ≤ 2.55359 := by
  have h := Real.exp_bound (x := (0.9375 : ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- Bounds on `exp 0.938` from the degree-7 Taylor bound. -/
private lemma exp_bounds_469_500 : 2.55483 ≤ Real.exp 0.938 ∧ Real.exp 0.938 ≤ 2.55487 := by
  have h := Real.exp_bound (x := (0.938 : ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- The characteristic function is positive at `1.875`. -/
private lemma cantileverChar_1875_pos : 0 < cantileverChar 1.875 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  set s : ℝ := 1.875 - Real.pi / 2 with hs
  have hcos : Real.cos 1.875 = -Real.sin s := by
    rw [hs, Real.sin_sub_pi_div_two, neg_neg]
  have hs1 : 0.3042035 < s := by rw [hs]; linarith
  have hs2 : s < 0.304204 := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  have hsb := Real.sin_bound (x := s) (by rw [abs_of_pos hs0]; linarith)
  rw [abs_of_pos hs0] at hsb
  have h3 : (0.3042035 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs1.le 3
  have h5 : s ^ 5 ≤ (0.304204 : ℝ) ^ 5 := pow_le_pow_left₀ hs0.le hs2.le 5
  have hsin_up : Real.sin s ≤ 0.29954 := by
    have := (abs_le.mp hsb).2
    norm_num at h3 h5
    linarith
  have hcosh : Real.cosh 1.875 ≤ 3.337091 := by
    obtain ⟨hE1, hE2⟩ := exp_bounds_15_16
    have he : Real.exp 1.875 = Real.exp 0.9375 * Real.exp 0.9375 := by
      rw [← Real.exp_add]
      norm_num
    rw [Real.cosh_eq, Real.exp_neg, he]
    have hEpos : 0 < Real.exp 0.9375 := Real.exp_pos _
    have hlo : (2.55355 : ℝ) * 2.55355 ≤ Real.exp 0.9375 * Real.exp 0.9375 :=
      mul_le_mul hE1 hE1 (by norm_num) hEpos.le
    have hup : Real.exp 0.9375 * Real.exp 0.9375 ≤ (2.55359 : ℝ) * 2.55359 :=
      mul_le_mul hE2 hE2 hEpos.le (by norm_num)
    have hinv : (Real.exp 0.9375 * Real.exp 0.9375)⁻¹ ≤ ((2.55355 : ℝ) * 2.55355)⁻¹ :=
      inv_anti₀ (by norm_num) hlo
    norm_num at hinv hup ⊢
    linarith
  have hcosh_pos := Real.cosh_pos (1.875 : ℝ)
  have hsin_pos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  unfold cantileverChar
  rw [hcos]
  nlinarith [mul_le_mul hsin_up hcosh hcosh_pos.le (by norm_num)]

/-- The characteristic function is negative at `1.876`. -/
private lemma cantileverChar_1876_neg : cantileverChar 1.876 < 0 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  set s : ℝ := 1.876 - Real.pi / 2 with hs
  have hcos : Real.cos 1.876 = -Real.sin s := by
    rw [hs, Real.sin_sub_pi_div_two, neg_neg]
  have hs1 : 0.3052035 < s := by rw [hs]; linarith
  have hs2 : s < 0.305204 := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  have hsb := Real.sin_bound (x := s) (by rw [abs_of_pos hs0]; linarith)
  rw [abs_of_pos hs0] at hsb
  have h3 : s ^ 3 ≤ (0.305204 : ℝ) ^ 3 := pow_le_pow_left₀ hs0.le hs2.le 3
  have h5 : s ^ 5 ≤ (0.305204 : ℝ) ^ 5 := pow_le_pow_left₀ hs0.le hs2.le 5
  have hsin_lo : 0.30043 ≤ Real.sin s := by
    have := (abs_le.mp hsb).1
    norm_num at h3 h5
    linarith
  have hcosh : 3.34017 ≤ Real.cosh 1.876 := by
    obtain ⟨hE1, hE2⟩ := exp_bounds_469_500
    have he : Real.exp 1.876 = Real.exp 0.938 * Real.exp 0.938 := by
      rw [← Real.exp_add]
      norm_num
    rw [Real.cosh_eq, Real.exp_neg, he]
    have hEpos : 0 < Real.exp 0.938 := Real.exp_pos _
    have hlo : (2.55483 : ℝ) * 2.55483 ≤ Real.exp 0.938 * Real.exp 0.938 :=
      mul_le_mul hE1 hE1 (by norm_num) hEpos.le
    have hup : Real.exp 0.938 * Real.exp 0.938 ≤ (2.55487 : ℝ) * 2.55487 :=
      mul_le_mul hE2 hE2 hEpos.le (by norm_num)
    have hinv : ((2.55487 : ℝ) * 2.55487)⁻¹ ≤ (Real.exp 0.938 * Real.exp 0.938)⁻¹ :=
      inv_anti₀ (by positivity) hup
    norm_num at hinv hlo ⊢
    linarith
  unfold cantileverChar
  rw [hcos]
  nlinarith [mul_le_mul hsin_lo hcosh (by norm_num) (by linarith)]

/-- A certified bracket around `1.8751`, a numerical illustration only:
`1.875 < z₁ < 1.876`. -/
lemma cantileverRoot_bracket : 1.875 < cantileverRoot ∧ cantileverRoot < 1.876 := by
  have hab : (1.875 : ℝ) ≤ 1.876 := by norm_num
  have hcont : Continuous cantileverChar := by
    unfold cantileverChar
    fun_prop
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hab hcont.continuousOn
    ⟨cantileverChar_1876_neg, cantileverChar_1875_pos⟩
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hzI : z ∈ Set.Ioo (Real.pi / 2) Real.pi := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  rw [← eq_cantileverRoot_of_mem_Ioo hzI hz0]
  exact hz

-- The first clamped-free mode on the beam `L = 2`, `EI = 3`, `ρA = 1` of section A meets the
-- four conditions, has a nonzero tip deflection and solves the beam equation at its frequency.
example :
    IsClampedFree 2 (cantileverMode 2 cantileverRoot) ∧ cantileverMode 2 cantileverRoot 2 ≠ 0 ∧
      1 * iteratedDeriv 2 (fun s : ℝ => cantileverMode 2 cantileverRoot 1 *
          Real.cos (cantileverFreq 3 1 2 cantileverRoot * s)) 0 +
        3 * iteratedDeriv 4 (fun y : ℝ => cantileverMode 2 cantileverRoot y *
          Real.cos (cantileverFreq 3 1 2 cantileverRoot * 0)) 1 = 0 := by
  obtain ⟨h1, h2, h3⟩ := cantileverFirstMode (EI := 3) (ρA := 1) (L := 2) (by norm_num) one_pos
    (by norm_num)
  exact ⟨h1, h2, h3 1 0⟩

-- At the least root the characteristic equation gives a nonzero clamped-free family member.
example : ∃ c : Fin 4 → ℝ, c ≠ 0 ∧ IsClampedFree 2 (modeFamily (cantileverRoot / 2) c) := by
  have h := isLeast_cantileverRoot.1
  refine (exists_isClampedFree_iff (div_pos h.1 two_pos) two_pos).2 ?_
  rw [div_mul_cancel₀ _ two_ne_zero]
  exact h.2

-- An invalid example: at `β L = π / 2` the characteristic function is `1`, so no nonzero family
-- member meets the clamped-free conditions.
example : ¬ ∃ c : Fin 4 → ℝ, c ≠ 0 ∧ IsClampedFree 1 (modeFamily (Real.pi / 2) c) := by
  rw [exists_isClampedFree_iff (by positivity) one_pos, mul_one]
  exact (cantileverChar_pos (by positivity) le_rfl).ne'

-- Doubling the length of the beam quarters every clamped-free frequency.
example (EI ρA L z : ℝ) : cantileverFreq EI ρA (2 * L) z = cantileverFreq EI ρA L z / 4 := by
  rw [cantileverFreq_length_scaling]
  norm_num

-- The old bracket `((2 k - 1) π / 2, k π)` fails at `k = 2`: `(3 π / 2, 2 π)` holds no root,
-- while a root lies in `(π, 3 π / 2)`.
example : (∃ z ∈ Set.Ioo Real.pi (3 * Real.pi / 2), cantileverChar z = 0) ∧
    ¬ ∃ z ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi), cantileverChar z = 0 :=
  ⟨secondRoot_lt_three_pi_div_two.1, fun ⟨z, hz, h⟩ => secondRoot_lt_three_pi_div_two.2 z hz h⟩

end PhyslibExtTest.Elasticity.BeamModes

end
