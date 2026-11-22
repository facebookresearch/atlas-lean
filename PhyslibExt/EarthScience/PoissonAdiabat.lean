/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Poisson relation for a reversible ideal-gas adiabat

For a reversible ideal-gas adiabat with constant mass-specific heat
capacity `cp`, the Poisson relation in ratio form is
`T₂ = T₁ * (p₂ / p₁) ^ (R / cp)`, where `R` is the mass-specific gas
constant. It is derived here from the ideal-gas law `p * v = R * T` at
two states and the adiabat `p₁ * v₁ ^ γ = p₂ * v₂ ^ γ` with
`γ = cp / (cp - R)`, together with the exponent identity
`(γ - 1) / γ = R / cp`. The companion module
`PhyslibExt.EarthScience.IdealGasAdiabatic` assumes this Poisson relation
to prove that potential temperature is constant along the adiabat; this
module proves the relation itself.

## i. Overview

`γ` is a real exponent, so `v ^ γ` is a real power. Positivity of all
pressures, volumes, and temperatures is used throughout.

## ii. Key results

- `EarthScience.poisson_exponent_identity`: `(γ - 1) / γ = R / cp`.
- `EarthScience.poisson_temperature_ratio`: the Poisson relation.

## iii. Table of contents

- A. Exponent identity
- B. Poisson temperature ratio

## iv. References

- John M. Wallace and Peter V. Hobbs, *Atmospheric Science: An Introductory
  Survey*, 2nd ed., Academic Press, 2006, §3.4.3, Eq. (3.54) (Poisson's
  equation for adiabatic motion with constant `R` and `cp`).
- `Real.div_rpow` / `Real.rpow_left_inj` / `Real.rpow_pos_of_pos` in Mathlib
  (real powers).
-/

@[expose] public section

namespace EarthScience

/-- Exponent identity: with `cv = cp - R` and `γ = cp / cv`, `(γ - 1) / γ = R / cp`. -/
theorem poisson_exponent_identity {R cp : ℝ} (hR : 0 < R) (h : R < cp) :
    (cp / (cp - R) - 1) / (cp / (cp - R)) = R / cp := by
  have hcp : 0 < cp := lt_trans hR h
  have hcv : (0:ℝ) < cp - R := sub_pos.mpr h
  have hcp0 : cp ≠ 0 := ne_of_gt hcp
  have hcv0 : cp - R ≠ 0 := ne_of_gt hcv
  field_simp
  ring

/-- Poisson relation for a reversible ideal-gas adiabat: from the ideal-gas
law `p * v = R * T` at two states and the adiabat `p₁ * v₁ ^ γ = p₂ * v₂ ^ γ`
with `γ = cp / (cp - R)`, the temperature ratio is
`T₂ = T₁ * (p₂ / p₁) ^ (R / cp)`. Here `v` is specific volume, `γ` a real
exponent (`^` is real power), and all pressures, volumes, temperatures are positive. -/
theorem poisson_temperature_ratio {p₁ p₂ v₁ v₂ T₁ T₂ R cp γ : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hT₁ : 0 < T₁) (hR : 0 < R) (h : R < cp) (hcp : 0 < cp)
    (hγ : γ = cp / (cp - R))
    (hgas₁ : p₁ * v₁ = R * T₁) (hgas₂ : p₂ * v₂ = R * T₂)
    (hadiabat : p₁ * v₁ ^ γ = p₂ * v₂ ^ γ) :
    T₂ = T₁ * (p₂ / p₁) ^ (R / cp) := by
  have hcv : (0:ℝ) < cp - R := sub_pos.mpr h
  have hγpos : 0 < γ := by
    rw [hγ]
    exact div_pos hcp hcv
  have hγ0 : γ ≠ 0 := ne_of_gt hγpos
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hq : 0 < p₂ / p₁ := div_pos hp₂ hp₁
  have hT₁eq : T₁ = p₁ * v₁ / R := by
    rw [eq_div_iff hR0]
    linarith [hgas₁]
  have hT₂eq : T₂ = p₂ * v₂ / R := by
    rw [eq_div_iff hR0]
    linarith [hgas₂]
  have hT₂pos : 0 < T₂ := by
    rw [hT₂eq]
    positivity
  have hexp : R / cp * γ = γ - 1 := by
    rw [hγ]
    have hcp0 : cp ≠ 0 := ne_of_gt hcp
    have hcv0 : cp - R ≠ 0 := ne_of_gt hcv
    field_simp
    ring
  have hqp : 0 < (p₂ / p₁) ^ (R / cp) := Real.rpow_pos_of_pos hq _
  have hrhs : 0 < T₁ * (p₂ / p₁) ^ (R / cp) := mul_pos hT₁ hqp
  have hvratio : v₂ ^ γ / v₁ ^ γ = p₁ / p₂ := by
    have hv₁p0 : v₁ ^ γ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hv₁ γ)
    have hp₂0 : p₂ ≠ 0 := ne_of_gt hp₂
    rw [div_eq_iff hv₁p0, div_mul_eq_mul_div, eq_div_iff hp₂0]
    linear_combination -hadiabat
  have hTratio : T₂ ^ γ / T₁ ^ γ = (p₂ / p₁) ^ (γ - 1) := by
    rw [hT₂eq, hT₁eq]
    have h2 : (0:ℝ) ≤ p₂ * v₂ / R := le_of_lt (div_pos (mul_pos hp₂ hv₂) hR)
    have h3 : (0:ℝ) ≤ p₁ * v₁ / R := le_of_lt (div_pos (mul_pos hp₁ hv₁) hR)
    rw [← Real.div_rpow h2 h3]
    have hfrac : (p₂ * v₂ / R) / (p₁ * v₁ / R) = (p₂ / p₁) * (v₂ / v₁) := by
      have hp₁0 : p₁ ≠ 0 := ne_of_gt hp₁
      have hv₁0 : v₁ ≠ 0 := ne_of_gt hv₁
      have h1 : p₁ * v₁ / R ≠ 0 := ne_of_gt (div_pos (mul_pos hp₁ hv₁) hR)
      field_simp
    rw [hfrac, Real.mul_rpow (le_of_lt hq) (le_of_lt (div_pos hv₂ hv₁)),
      Real.div_rpow (le_of_lt hv₂) (le_of_lt hv₁), hvratio]
    have e2 : (p₂ / p₁) ^ (γ - 1) = (p₂ / p₁) ^ γ * (p₁ / p₂) := by
      have h1' : (p₂ / p₁) ^ (-1 : ℝ) = p₁ / p₂ := by
        rw [Real.rpow_neg (le_of_lt hq), Real.rpow_one, inv_div]
      have h2' : γ - 1 = γ + (-1) := by ring
      rw [h2', Real.rpow_add hq, h1']
    rw [e2]
  have hT₁pow0 : T₁ ^ γ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hT₁ γ)
  have hTv : T₂ ^ γ = T₁ ^ γ * (p₂ / p₁) ^ (γ - 1) := by
    have h := (div_eq_iff hT₁pow0).mp hTratio
    rw [h, mul_comm]
  have e1 : (T₁ * (p₂ / p₁) ^ (R / cp)) ^ γ
      = T₁ ^ γ * (p₂ / p₁) ^ (γ - 1) := by
    rw [Real.mul_rpow (le_of_lt hT₁) (le_of_lt hqp),
      ← Real.rpow_mul (le_of_lt hq), hexp]
  apply (Real.rpow_left_inj (le_of_lt hT₂pos) (le_of_lt hrhs) hγ0).mp
  rw [e1, hTv]
end EarthScience
