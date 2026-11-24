/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import PhyslibExt.ClassicalMechanics.Acoustics.Transmission
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Effective transmission loss of parallel patches

## i. Overview

For two equal-area patches under uniform incident intensity
with positive transmission coefficients `τ1`, `τ2`, the effective
coefficient is the area average `(τ1 + τ2) / 2` (the
uniform-intensity case of the power-weighted average
`Acoustics.effectivePowerTransmission`), and its loss
`-10 * log10 ((τ1 + τ2) / 2)` lies between the two patch losses.
For distinct coefficients it is strictly below the average of
the two decibel values: averaging decibels is not the effective
loss. With non-uniform incident intensity the effective
coefficient is intensity-weighted instead, and the arithmetic
mean does not apply.

## ii. Key results

- `Acoustics.effective_loss_between`: the effective loss is
  between the patch losses.
- `Acoustics.effective_loss_lt_db_average`: the effective loss is
  strictly below the decibel average for distinct coefficients.
- `Acoustics.effectivePowerTransmission_two_patch_eq`: the
  uniform-intensity two-patch effective coefficient is the
  arithmetic mean, through `effectivePowerTransmission`.
- `Acoustics.effectivePowerTransmission_loss_between` and
  `Acoustics.effectivePowerTransmission_loss_lt_db_average`: the
  bounds stated for that effective coefficient.

## iii. Table of contents

- A. Effective loss bounds

## iv. References

- L. L. Beranek and I. L. Vér (eds.), *Noise and Vibration
  Control Engineering*, Wiley, 1992 (composite transmission loss
  of parallel elements under uniform incident intensity).
-/

@[expose] public section

namespace Acoustics

/-! ## A. Effective loss bounds -/

/-- Effective transmission loss of two parallel patches lies
between the two patch losses: for positive transmission
coefficients `τ1`, `τ2`, the loss `-10 * log10 ((τ1 + τ2) / 2)` of
the area-averaged coefficient is at least the smaller patch loss
`-10 * log10 (max τ1 τ2)` and at most the larger patch loss
`-10 * log10 (min τ1 τ2)`. -/
theorem effective_loss_between {τ1 τ2 : ℝ} (h1 : 0 < τ1)
    (h2 : 0 < τ2) :
    -10 * Real.logb 10 (max τ1 τ2)
        ≤ -10 * Real.logb 10 ((τ1 + τ2) / 2)
      ∧ -10 * Real.logb 10 ((τ1 + τ2) / 2)
        ≤ -10 * Real.logb 10 (min τ1 τ2) := by
  have h10 : (1:ℝ) < 10 := by norm_num
  have havg_pos : (0:ℝ) < (τ1 + τ2) / 2 := by linarith
  have hmin_le : min τ1 τ2 ≤ (τ1 + τ2) / 2 := by
    have a := min_le_left τ1 τ2
    have b := min_le_right τ1 τ2
    linarith
  have hmax_le : (τ1 + τ2) / 2 ≤ max τ1 τ2 := by
    have a := le_max_left τ1 τ2
    have b := le_max_right τ1 τ2
    linarith
  have hmin_pos : (0:ℝ) < min τ1 τ2 := lt_min h1 h2
  have e1 := Real.logb_le_logb_of_le h10 havg_pos hmax_le
  have e2 := Real.logb_le_logb_of_le h10 hmin_pos hmin_le
  refine ⟨?_, ?_⟩ <;> linarith

/-- Averaging decibel values is not the effective loss: for
distinct positive coefficients the area-averaged loss is strictly
below the average of the two patch losses (arithmetic-geometric
mean gap). Equal areas with `τ = 0.001` and `τ = 0.1` give about
`12.97 dB`, not the `20 dB` average of `30 dB` and `10 dB`. -/
theorem effective_loss_lt_db_average {τ1 τ2 : ℝ} (h1 : 0 < τ1)
    (h2 : 0 < τ2) (hne : τ1 ≠ τ2) :
    -10 * Real.logb 10 ((τ1 + τ2) / 2)
      < (-10 * Real.logb 10 τ1 + -10 * Real.logb 10 τ2) / 2 := by
  have h10 : (1:ℝ) < 10 := by norm_num
  have hprod_pos : (0:ℝ) < τ1 * τ2 := mul_pos h1 h2
  have hsq : τ1 * τ2 < ((τ1 + τ2) / 2) ^ 2 := by
    have hpos : (0:ℝ) < (τ1 - τ2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith [hpos]
  have hlog := Real.logb_lt_logb h10 hprod_pos hsq
  rw [Real.logb_mul (ne_of_gt h1) (ne_of_gt h2)] at hlog
  have hpow : Real.logb 10 (((τ1 + τ2) / 2) ^ 2)
      = 2 * Real.logb 10 ((τ1 + τ2) / 2) := by
    rw [Real.logb_pow]
    norm_num
  rw [hpow] at hlog
  linarith

/-- Two-patch uniform-intensity specialization of the effective
power transmission coefficient: for two patches of equal area
`A > 0` under uniform incident intensity `I0 > 0`, the effective
coefficient `Acoustics.effectivePowerTransmission` is the
arithmetic mean `(τ1 + τ2) / 2`. -/
theorem effectivePowerTransmission_two_patch_eq {τ1 τ2 A I0 : ℝ}
    (hI0 : 0 < I0) (hA : 0 < A) :
    effectivePowerTransmission (fun _ : Fin 2 => I0)
        (fun _ : Fin 2 => A) (fun i : Fin 2 => if i = 0 then τ1 else τ2)
        Finset.univ
      = (τ1 + τ2) / 2 := by
  rw [effectivePowerTransmission_eq_of_uniform _ _ _ _ hI0
    (fun i _ => rfl)]
  have hA' : A ≠ 0 := ne_of_gt hA
  have e1 : (fun i : Fin 2 => if i = 0 then τ1 else τ2) 1 = τ2 :=
    if_neg (by decide)
  simp only [Fin.sum_univ_two, e1]
  field_simp
  split_ifs <;> ring

/-- The effective loss of the two-patch effective coefficient
lies between the two patch losses. -/
theorem effectivePowerTransmission_loss_between {τ1 τ2 A I0 : ℝ}
    (hI0 : 0 < I0) (hA : 0 < A) (h1 : 0 < τ1) (h2 : 0 < τ2) :
    -10 * Real.logb 10 (max τ1 τ2)
        ≤ -10 * Real.logb 10
          (effectivePowerTransmission (fun _ : Fin 2 => I0)
            (fun _ : Fin 2 => A) (fun i : Fin 2 => if i = 0 then τ1 else τ2)
            Finset.univ)
      ∧ -10 * Real.logb 10
          (effectivePowerTransmission (fun _ : Fin 2 => I0)
            (fun _ : Fin 2 => A) (fun i : Fin 2 => if i = 0 then τ1 else τ2)
            Finset.univ)
        ≤ -10 * Real.logb 10 (min τ1 τ2) := by
  rw [effectivePowerTransmission_two_patch_eq hI0 hA]
  exact effective_loss_between h1 h2

/-- The effective loss of the two-patch effective coefficient is
strictly below the decibel average for distinct coefficients. -/
theorem effectivePowerTransmission_loss_lt_db_average
    {τ1 τ2 A I0 : ℝ} (hI0 : 0 < I0) (hA : 0 < A) (h1 : 0 < τ1)
    (h2 : 0 < τ2) (hne : τ1 ≠ τ2) :
    -10 * Real.logb 10
        (effectivePowerTransmission (fun _ : Fin 2 => I0)
          (fun _ : Fin 2 => A) (fun i : Fin 2 => if i = 0 then τ1 else τ2)
          Finset.univ)
      < (-10 * Real.logb 10 τ1 + -10 * Real.logb 10 τ2) / 2 := by
  rw [effectivePowerTransmission_two_patch_eq hI0 hA]
  exact effective_loss_lt_db_average h1 h2 hne

end Acoustics
