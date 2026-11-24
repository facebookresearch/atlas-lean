/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hertzian dipole power, directivity and resistance

## i. Overview

The far-field intensity of a Hertzian (infinitesimal,
uniform-current) dipole is `K sin²θ`. Throughout, "dipole" means
this Hertzian element; the finite short dipole with triangular
current (effective length `l/2`) is a different element whose
intensity coefficient and resistance are four times smaller, and
is not modeled here. Integrating over the sphere, the total
radiated power is `8πK/3`, the directivity is `3 sin²θ/2` with
maximum `3/2` broadside and zeros on the axis, and the radiation
resistance, under the peak-amplitude convention `R = 2P/I²`, is
`16πK/(3I²)`. A zero drive gives zero power, and the on-axis
directivity is not the maximum.

## ii. Key results

- `radiatedPower_shortDipoleIntensity`: total power `8πK/3`.
- `directivity_shortDipoleIntensity`: directivity `3 sin²θ/2`.
- `isGreatest_directivity_shortDipoleIntensity`: `3/2` is the
  greatest directivity over the polar range.
- `radiationResistance_shortDipole`: the peak-convention
  resistance.

## iii. Table of contents

- A. Short-dipole radiation metrics

## iv. References

- C. A. Balanis, *Antenna Theory: Analysis and Design*, fourth
edition, Wiley, 2016: the Hertzian dipole, its `sin²θ` pattern,
  directivity `1.5`, and radiation resistance.

## A. Short-dipole radiation metrics
-/

@[expose] public section

namespace PhyslibExt.Electromagnetism.ShortDipoleMetrics

open Real

/-- Declared Hertzian short-dipole far-field radiation intensity `U(θ) = K sin²θ`. -/
noncomputable def shortDipoleIntensity (K θ : ℝ) : ℝ :=
  K * Real.sin θ ^ 2

/-- Total radiated power of an azimuthally symmetric intensity pattern `U(θ)`, integrated
against the solid-angle measure `sin θ dθ dφ` over `θ ∈ [0, π]`, `φ ∈ [0, 2π]`. -/
noncomputable def radiatedPower (U : ℝ → ℝ) : ℝ :=
  ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π, U θ * Real.sin θ

/-- Directivity `D(θ) = 4π U(θ) / P_rad`, for a pattern of positive radiated power. For zero
radiated power the value is `0` (`x / 0 = 0`), which is not a directivity
(`directivity_shortDipoleIntensity_zero_ne`); the results that use it assume `P_rad ≠ 0`. -/
noncomputable def directivity (U : ℝ → ℝ) (θ : ℝ) : ℝ :=
  4 * π * U θ / radiatedPower U

/-- Intensity coefficient `K = η k² I_peak² l² / (32 π²)` of a
Hertzian (infinitesimal) dipole element: a uniform-current
element whose effective length equals its physical length `l`.
This is not the finite short dipole with triangular current
distribution, whose effective length is `l / 2` and whose
coefficient is four times smaller. -/
noncomputable def shortDipoleIntensityCoeff (η k Ipeak l : ℝ) : ℝ :=
  η * k ^ 2 * Ipeak ^ 2 * l ^ 2 / (32 * π ^ 2)

/-- Radiation resistance in the peak-amplitude convention `P_rad = ½ I_peak² R_rad`. -/
noncomputable def radiationResistance (Prad Ipeak : ℝ) : ℝ :=
  2 * Prad / Ipeak ^ 2

private theorem integral_sin_cubed : ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 3 = 4 / 3 := by
  have h := integral_sin_pow_odd (n := 1)
  rw [Finset.prod_range_one] at h
  simp only [Nat.cast_zero, mul_zero, zero_add] at h
  have h2 : (2 : ℝ) * (2 / 3) = 4 / 3 := by norm_num
  rw [h2] at h
  exact h

private theorem pi_div_two_mem_Icc : (π / 2 : ℝ) ∈ Set.Icc 0 π := by
  constructor
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

/-- **Short-dipole radiated power** `P_rad = 8πK/3`. -/
lemma radiatedPower_shortDipoleIntensity (K : ℝ) (hK : 0 < K) :
    radiatedPower (shortDipoleIntensity K) = 8 * π * K / 3 := by
  have hfun : (fun θ : ℝ => shortDipoleIntensity K θ * Real.sin θ)
      = fun θ => K * (Real.sin θ ^ 3) := by
    funext θ
    simp only [shortDipoleIntensity]
    ring
  unfold radiatedPower
  rw [hfun, intervalIntegral.integral_const_mul, integral_sin_cubed,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Short-dipole directivity** `D(θ) = 3 sin²θ / 2`. -/
lemma directivity_shortDipoleIntensity (K : ℝ) (hK : 0 < K) (θ : ℝ) :
    directivity (shortDipoleIntensity K) θ = 3 * Real.sin θ ^ 2 / 2 := by
  have hP := radiatedPower_shortDipoleIntensity K hK
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hK' : K ≠ 0 := ne_of_gt hK
  have hden : (8 : ℝ) * π * K / 3 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) hK') (by norm_num)
  unfold directivity
  rw [hP]
  unfold shortDipoleIntensity
  rw [div_eq_iff hden]
  ring

/-- **Maximum directivity** `3/2`: it is the greatest value of `D` on `θ ∈ [0, π]`. -/
lemma isGreatest_directivity_shortDipoleIntensity (K : ℝ) (hK : 0 < K) :
    IsGreatest (directivity (shortDipoleIntensity K) '' Set.Icc 0 π) (3 / 2) := by
  constructor
  · exact ⟨π / 2, pi_div_two_mem_Icc, by
      rw [directivity_shortDipoleIntensity K hK, Real.sin_pi_div_two]
      norm_num⟩
  · intro y hy
    obtain ⟨θ, hθ, rfl⟩ := hy
    rw [directivity_shortDipoleIntensity K hK]
    have h := Real.sin_sq_le_one θ
    linarith

/-- **Short-dipole radiation resistance** `R_rad = η k² l² / (6π)` for
`K = η k² I_peak² l² / (32 π²)`. -/
lemma radiationResistance_shortDipole (η k Ipeak l : ℝ) (hη : 0 < η) (hk : 0 < k)
    (hIpeak : 0 < Ipeak) (hl : 0 < l) :
    radiationResistance
        (radiatedPower (shortDipoleIntensity (shortDipoleIntensityCoeff η k Ipeak l)))
        Ipeak =
      η * k ^ 2 * l ^ 2 / (6 * π) := by
  have hk2 : (0 : ℝ) < k ^ 2 := pow_pos hk 2
  have hI2 : (0 : ℝ) < Ipeak ^ 2 := pow_pos hIpeak 2
  have hl2 : (0 : ℝ) < l ^ 2 := pow_pos hl 2
  have hpi2 : (0 : ℝ) < (π : ℝ) ^ 2 := pow_pos Real.pi_pos 2
  have hK : 0 < shortDipoleIntensityCoeff η k Ipeak l := by
    unfold shortDipoleIntensityCoeff
    exact div_pos (mul_pos (mul_pos (mul_pos hη hk2) hI2) hl2)
      (mul_pos (by norm_num) hpi2)
  have hP := radiatedPower_shortDipoleIntensity _ hK
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hI : Ipeak ≠ 0 := ne_of_gt hIpeak
  have hIn2 : Ipeak ^ 2 ≠ 0 := ne_of_gt hI2
  have hpin2 : (π : ℝ) ^ 2 ≠ 0 := ne_of_gt hpi2
  have h32 : (32 : ℝ) * π ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hpin2
  have h6 : (6 : ℝ) * π ≠ 0 := mul_ne_zero (by norm_num) hpi
  unfold radiationResistance
  rw [hP]
  unfold shortDipoleIntensityCoeff
  field_simp
  ring

/-- Any pattern with nonzero radiated power has directivity normalized to `4π` over the
sphere. -/
lemma radiatedPower_directivity (U : ℝ → ℝ) (hU : radiatedPower U ≠ 0) :
    radiatedPower (directivity U) = 4 * π := by
  have hfun : (fun θ : ℝ => directivity U θ * Real.sin θ)
      = fun θ => (4 * π / radiatedPower U) * (U θ * Real.sin θ) := by
    funext θ
    unfold directivity
    ring
  have hUeq : radiatedPower U
      = (2 * π - 0) * ∫ θ in (0 : ℝ)..π, U θ * Real.sin θ := by
    unfold radiatedPower
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hDeq : radiatedPower (directivity U)
      = (2 * π - 0) * ∫ θ in (0 : ℝ)..π, directivity U θ * Real.sin θ := by
    unfold radiatedPower
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hinner : ∫ θ in (0 : ℝ)..π, directivity U θ * Real.sin θ
      = (4 * π / radiatedPower U) * ∫ θ in (0 : ℝ)..π, U θ * Real.sin θ := by
    rw [hfun, intervalIntegral.integral_const_mul]
  rw [hDeq, hinner]
  calc (2 * π - 0) * ((4 * π / radiatedPower U) * ∫ θ in (0 : ℝ)..π, U θ * Real.sin θ)
      = (4 * π / radiatedPower U) * ((2 * π - 0) * ∫ θ in (0 : ℝ)..π, U θ * Real.sin θ) := by
        ring
    _ = (4 * π / radiatedPower U) * radiatedPower U := by
        congr 1
        exact hUeq.symm
    _ = 4 * π := div_mul_cancel₀ _ hU

/-- Validation: the maximum `3/2` is attained on `[0, π]` exactly at `θ = π/2`. -/
lemma directivity_shortDipoleIntensity_eq_max_iff (K : ℝ) (hK : 0 < K) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 π) :
    directivity (shortDipoleIntensity K) θ = 3 / 2 ↔ θ = π / 2 := by
  rw [directivity_shortDipoleIntensity K hK]
  constructor
  · intro h
    have hsin2 : Real.sin θ ^ 2 = 1 := by linarith
    have hsc := Real.sin_sq_add_cos_sq θ
    have hcos2 : Real.cos θ ^ 2 = 0 := by linarith
    have hcos : Real.cos θ = 0 := sq_eq_zero_iff.mp hcos2
    have hinj := Real.strictAntiOn_cos.injOn
    exact hinj hθ pi_div_two_mem_Icc (by rw [hcos, Real.cos_pi_div_two])
  · intro h
    rw [h, Real.sin_pi_div_two]
    norm_num

/-- Validation: null intensity on the dipole axis, `θ = 0` and `θ = π`. -/
lemma shortDipoleIntensity_on_axis (K : ℝ) :
    shortDipoleIntensity K 0 = 0 ∧ shortDipoleIntensity K π = 0 := by
  simp [shortDipoleIntensity, Real.sin_zero, Real.sin_pi]

/-- Validation: null directivity on the dipole axis, `θ = 0` and `θ = π`. -/
lemma directivity_shortDipoleIntensity_on_axis (K : ℝ) (hK : 0 < K) :
    directivity (shortDipoleIntensity K) 0 = 0 ∧ directivity (shortDipoleIntensity K) π = 0 := by
  rw [directivity_shortDipoleIntensity K hK, directivity_shortDipoleIntensity K hK]
  simp [Real.sin_zero, Real.sin_pi]

/-- Validation: full angular normalization of the short-dipole directivity,
`∫∫ D(θ) sin θ dθ dφ = 4π`. -/
lemma radiatedPower_directivity_shortDipoleIntensity (K : ℝ) (hK : 0 < K) :
    radiatedPower (directivity (shortDipoleIntensity K)) = 4 * π := by
  apply radiatedPower_directivity
  rw [radiatedPower_shortDipoleIntensity K hK]
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) < π * K := mul_pos hpi hK
  have hpos : (0 : ℝ) < 8 * π * K / 3 := by nlinarith [h1]
  exact ne_of_gt hpos

/-- Validation, `K = 0`: zero radiated power. -/
lemma radiatedPower_shortDipoleIntensity_zero :
    radiatedPower (shortDipoleIntensity 0) = 0 := by
  have hfun : (fun θ : ℝ => shortDipoleIntensity 0 θ * Real.sin θ) = fun _ => (0 : ℝ) := by
    funext θ
    simp [shortDipoleIntensity]
  unfold radiatedPower
  rw [hfun]
  simp

/-- Validation, `K = 0`: the ratio-defined directivity is not the short-dipole pattern
(at `θ = π/2` it is not `3/2`), so `K > 0` is needed for the directivity claim. -/
lemma directivity_shortDipoleIntensity_zero_ne :
    directivity (shortDipoleIntensity 0) (π / 2) ≠ 3 / 2 := by
  have hP := radiatedPower_shortDipoleIntensity_zero
  have hU : shortDipoleIntensity 0 (π / 2) = 0 := by simp [shortDipoleIntensity]
  unfold directivity
  rw [hP, hU, mul_zero, zero_div]
  norm_num

end PhyslibExt.Electromagnetism.ShortDipoleMetrics
