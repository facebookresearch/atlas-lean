/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.KineticTheory

/-!
# Kinetic theory of gases checks

Concrete consumers of `PhyslibExt.Chemistry.KineticTheory`: normalization for a stated gas,
the three characteristic speeds of `O₂` at `300 K`, the speed ordering, both pressure lemmas on
a three-particle ensemble, and Graham's ratio for `H₂` and `O₂`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The numeric gas is `O₂` with
`M = 0.032` kg/mol at `T = 300` K and `R = 8.314` J/(mol K). Speeds are given by exact symbolic
values and verified bounds, never by decimal equalities. The pressure checks use a cube of side
`1` holding three particles of mass `2` moving with speed `3` along `x`, `y` and `z`; this
ensemble is isotropic with `⟨v²⟩ = 9`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Normalization
- B. Characteristic speeds of O₂ at 300 K
- C. Pressure lemmas
- D. Effusion

## iv. References

- `PhyslibExt.Chemistry.KineticTheory`

## A. Normalization
-/

open Chemistry.KineticTheory
open scoped BigOperators

/-- Normalization of `mbSpeed` at `R = 8.314`, `T = 300`, `M = 0.032`. -/
example : ∫ v in Set.Ioi (0 : ℝ), mbSpeed 8.314 300 0.032 v = 1 :=
  integral_mbSpeed (by norm_num) (by norm_num) (by norm_num)

/-- The density at the stated gas is integrable on `(0, ∞)`, since its integral is `1 ≠ 0`. -/
example : MeasureTheory.IntegrableOn (mbSpeed 8.314 300 0.032) (Set.Ioi 0) :=
  MeasureTheory.Integrable.of_integral_ne_zero <| by
    rw [integral_mbSpeed (by norm_num) (by norm_num) (by norm_num)]
    exact one_ne_zero

/-- Nonnegativity on `[0, ∞)` at the stated gas. -/
example (v : ℝ) (_ : 0 ≤ v) : 0 ≤ mbSpeed 8.314 300 0.032 v :=
  mbSpeed_nonneg (by norm_num) (by norm_num) (by norm_num) v

/-! ## B. Characteristic speeds of O₂ at 300 K -/

/-- Exact value `v_mp = √155887.5`. -/
example : mostProbableSpeed 8.314 300 0.032 = Real.sqrt 155887.5 := by
  rw [mostProbableSpeed]
  norm_num

/-- `394 < v_mp < 395` (m/s). -/
example : 394 < mostProbableSpeed 8.314 300 0.032 ∧ mostProbableSpeed 8.314 300 0.032 < 395 := by
  rw [mostProbableSpeed]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- Exact value `⟨v⟩ = √(623550 / π)`. -/
example : meanSpeed 8.314 300 0.032 = Real.sqrt (623550 / Real.pi) := by
  rw [meanSpeed_eq (by norm_num) (by norm_num) (by norm_num)]
  congr 1
  field_simp
  norm_num

/-- `445 < ⟨v⟩ < 446` (m/s), from `Real.pi_lt_d4 : π < 3.1416` and
`Real.pi_gt_d2 : 3.14 < π`. -/
example : 445 < meanSpeed 8.314 300 0.032 ∧ meanSpeed 8.314 300 0.032 < 446 := by
  rw [meanSpeed_eq (by norm_num) (by norm_num) (by norm_num)]
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d4]
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ (by positivity)]
    linarith [Real.pi_gt_d2]

/-- Exact value `v_rms = √233831.25`. -/
example : rmsSpeed 8.314 300 0.032 = Real.sqrt 233831.25 := by
  rw [rmsSpeed_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `483 < v_rms < 484` (m/s). -/
example : 483 < rmsSpeed 8.314 300 0.032 ∧ rmsSpeed 8.314 300 0.032 < 484 := by
  rw [rmsSpeed_eq (by norm_num) (by norm_num) (by norm_num)]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- `v_mp < ⟨v⟩ < v_rms` at the stated gas. -/
example : mostProbableSpeed 8.314 300 0.032 < meanSpeed 8.314 300 0.032 ∧
    meanSpeed 8.314 300 0.032 < rmsSpeed 8.314 300 0.032 :=
  ⟨mostProbableSpeed_lt_meanSpeed (by norm_num) (by norm_num) (by norm_num),
    meanSpeed_lt_rmsSpeed (by norm_num) (by norm_num) (by norm_num)⟩

/-- `v_mp < ⟨v⟩ < v_rms` in general. -/
example {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    mostProbableSpeed R T M < meanSpeed R T M ∧ meanSpeed R T M < rmsSpeed R T M :=
  ⟨mostProbableSpeed_lt_meanSpeed hR hT hM, meanSpeed_lt_rmsSpeed hR hT hM⟩

/-- `v_mp` maximizes the density on `[0, ∞)` at the stated gas. -/
example : IsMaxOn (mbSpeed 8.314 300 0.032) (Set.Ici 0) (mostProbableSpeed 8.314 300 0.032) :=
  (isMaxOn_mbSpeed_iff (by norm_num) (by norm_num) (by norm_num) (Real.sqrt_nonneg _)).mpr rfl

/-- Uniqueness: `400` m/s, close to `v_mp`, is not a maximizer on `[0, ∞)`. -/
example : ¬ IsMaxOn (mbSpeed 8.314 300 0.032) (Set.Ici 0) 400 := by
  rw [isMaxOn_mbSpeed_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    mostProbableSpeed]
  intro h
  have h' : Real.sqrt (2 * 8.314 * 300 / 0.032) < 395 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-! ## C. Pressure lemmas -/

/-- The three-particle ensemble is isotropic with `⟨v²⟩ = 9`, and `9` is its mean square
speed. -/
example :
    ((𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![3, 0, 0] : Fin 3 → ℝ) i ^ 2) =
        𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 3, 0] : Fin 3 → ℝ) i ^ 2 ∧
      (𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 3, 0] : Fin 3 → ℝ) i ^ 2) =
        𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 0, 3] : Fin 3 → ℝ) i ^ 2 ∧
      (𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 0, 3] : Fin 3 → ℝ) i ^ 2) = 1 / 3 * 9) ∧
    𝔼 i ∈ (Finset.univ : Finset (Fin 3)), ((![3, 0, 0] : Fin 3 → ℝ) i ^ 2 +
      (![0, 3, 0] : Fin 3 → ℝ) i ^ 2 + (![0, 0, 3] : Fin 3 → ℝ) i ^ 2) = 9 := by
  have hiso : ((𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![3, 0, 0] : Fin 3 → ℝ) i ^ 2) =
        𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 3, 0] : Fin 3 → ℝ) i ^ 2 ∧
      (𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 3, 0] : Fin 3 → ℝ) i ^ 2) =
        𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 0, 3] : Fin 3 → ℝ) i ^ 2 ∧
      (𝔼 i ∈ (Finset.univ : Finset (Fin 3)), (![0, 0, 3] : Fin 3 → ℝ) i ^ 2) = 1 / 3 * 9) := by
    simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_three, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  exact ⟨hiso, expect_speed_sq_of_isotropy hiso⟩

/-- Pressure from the definition: the particle moving along `x` transfers `2 * 2 * 3 = 12` per
collision every `2 * 1 / 3`, and the two particles with `vx = 0` contribute `0`, so `p = 18` on
the unit wall. -/
example : wallPressure (Finset.univ : Finset (Fin 3))
    (fun i => 2 * 2 * |(![3, 0, 0] : Fin 3 → ℝ) i|)
    (fun i => 2 * 1 / |(![3, 0, 0] : Fin 3 → ℝ) i|) (1 ^ 2) = 18 := by
  simp only [wallPressure, Fin.sum_univ_three]
  norm_num

/-- `p * V = (1 / 3) * N * m * ⟨v²⟩ = 18` for the ensemble, with no identification
hypothesis. -/
example : wallPressure (Finset.univ : Finset (Fin 3))
    (fun i => 2 * 2 * |(![3, 0, 0] : Fin 3 → ℝ) i|)
    (fun i => 2 * 1 / |(![3, 0, 0] : Fin 3 → ℝ) i|) (1 ^ 2) * 1 = 1 / 3 * 3 * 2 * 9 :=
  wallPressure_mul_volume (vy := ![0, 3, 0]) (vz := ![0, 0, 3]) one_pos (by norm_num)
    (by simp) (by norm_num) (by norm_num) (fun _ _ => rfl) (fun _ _ => rfl) <| by
      simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_three, Finset.card_univ,
        Fintype.card_fin]
      norm_num

/-- Without the identification hypothesis the wall model does not give `p * V = N * kB * T`:
for `kB = 1`, `T = 1` the ensemble has `p * V = 18 ≠ 3 = N * kB * T`. -/
example : wallPressure (Finset.univ : Finset (Fin 3))
    (fun i => 2 * 2 * |(![3, 0, 0] : Fin 3 → ℝ) i|)
    (fun i => 2 * 1 / |(![3, 0, 0] : Fin 3 → ℝ) i|) (1 ^ 2) * 1 ≠ 3 * 1 * 1 := by
  rw [wallPressure_mul_volume (vy := ![0, 3, 0]) (vz := ![0, 0, 3]) (m := 2) (N := 3) (v2 := 9)
    one_pos (by norm_num) (by simp) (by norm_num) (by norm_num) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_three, Finset.card_univ,
        Fintype.card_fin]
      norm_num)]
  norm_num

/-- With `Ek = (1 / 2) * 2 * 9 = 9` and the identification `Ek = (3 / 2) * kB * T` at `kB = 2`,
`T = 3`, the consistency step gives `p * V = N * kB * T = 18`. -/
example : wallPressure (Finset.univ : Finset (Fin 3))
    (fun i => 2 * 2 * |(![3, 0, 0] : Fin 3 → ℝ) i|)
    (fun i => 2 * 1 / |(![3, 0, 0] : Fin 3 → ℝ) i|) (1 ^ 2) * 1 = 3 * 2 * 3 :=
  wallPressure_mul_volume_of_kineticEnergy (vy := ![0, 3, 0]) (vz := ![0, 0, 3]) (v2 := 9)
    (Ek := 9) one_pos (by norm_num) (by simp) (by norm_num) (by norm_num) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (by
      simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_three, Finset.card_univ,
        Fintype.card_fin]
      norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Molar form with the bridges `N = n * NA` (`3 = (1 / 2) * 6`) and `R = NA * kB`
(`12 = 6 * 2`): `p * V = n * R * T = 18`. -/
example : wallPressure (Finset.univ : Finset (Fin 3))
    (fun i => 2 * 2 * |(![3, 0, 0] : Fin 3 → ℝ) i|)
    (fun i => 2 * 1 / |(![3, 0, 0] : Fin 3 → ℝ) i|) (1 ^ 2) * 1 = 1 / 2 * 12 * 3 :=
  wallPressure_mul_volume_molar (vy := ![0, 3, 0]) (vz := ![0, 0, 3]) (v2 := 9) (Ek := 9)
    (kB := 2) (N := 3) (NA := 6) one_pos (by norm_num) (by simp) (by norm_num) (by norm_num)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_three, Finset.card_univ,
        Fintype.card_fin]
      norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## D. Effusion -/

/-- Graham's ratio for `H₂` (`M = 0.002`) and `O₂` (`M = 0.032`) at `300 K`:
`M_O₂ / M_H₂ = 16`, so `rate_H₂ / rate_O₂ = 4` exactly. -/
example {k rateH2 rateO2 : ℝ} (hk : 0 < k) (hH2 : rateH2 = k * meanSpeed 8.314 300 0.002)
    (hO2 : rateO2 = k * meanSpeed 8.314 300 0.032) : rateH2 / rateO2 = 4 := by
  rw [effusion_rate_ratio (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk rfl hH2 hO2,
    show (0.032 : ℝ) / 0.002 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `rate ∝ √(T / M)`: doubling `T` at fixed `M` and `k` multiplies the rate by `√2`. -/
example {k r₁ r₂ : ℝ} (h₁ : r₁ = k * meanSpeed 8.314 300 0.032)
    (h₂ : r₂ = k * meanSpeed 8.314 600 0.032) : r₂ = Real.sqrt 2 * r₁ := by
  rw [effusion_rate_eq (by norm_num) (by norm_num) (by norm_num) h₂,
    effusion_rate_eq (by norm_num) (by norm_num) (by norm_num) h₁,
    show (600 : ℝ) / 0.032 = 2 * (300 / 0.032) by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Non-claim: equal molar masses at `300 K` and `600 K` do not effuse at equal rates. -/
example {k r₁ r₂ : ℝ} (hk : 0 < k) (h₁ : r₁ = k * meanSpeed 8.314 300 0.032)
    (h₂ : r₂ = k * meanSpeed 8.314 600 0.032) : r₁ ≠ r₂ :=
  effusion_rate_ne_of_temperature_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
    rfl h₁ h₂ (by norm_num)

/-- Compensation: `H₂` at `300 K` and `O₂` at `4800 K` have equal `T / M = 150000`, so equal
rates. -/
example {k r₁ r₂ : ℝ} (hk : 0 < k) (h₁ : r₁ = k * meanSpeed 8.314 300 0.002)
    (h₂ : r₂ = k * meanSpeed 8.314 4800 0.032) : r₁ = r₂ :=
  (effusion_rate_eq_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk rfl h₁ h₂).mpr (by norm_num)
