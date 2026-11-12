 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# One-layer grey atmosphere

## i. Overview

For one IR-grey, shortwave-transparent atmosphere with emissivity
`eps ∈ [0,1]`, the surface/atmosphere energy balances yield
`Ts^4 = Te^4 / (1 - eps/2)`. The atmosphere equilibrium is
`2*eps*sigma*Ta^4 = eps*sigma*Ts^4` and the top-of-atmosphere balance is
`sigma*Te^4 = (1-eps)*sigma*Ts^4 + eps*sigma*Ta^4`. `Te` is the effective
temperature, `Ts` the surface temperature, `Ta` the atmosphere temperature,
and `sigma` the Stefan–Boltzmann model parameter. No scattering or cloud
feedback is claimed; `eps = 0` is handled without division by `eps`.

## ii. Key results

- `EarthScience.atmosphere_temperature`: `Ta^4 = Ts^4 / 2` for `eps > 0`.
- `EarthScience.surface_temperature`: balances yield `Ts^4 = Te^4 / (1 - eps/2)`.
- `EarthScience.transparent_limit`: `eps = 0` gives `Ts^4 = Te^4`.
- `EarthScience.opaque_witness`: `eps = 1` gives `Ts^4 = 2 * Te^4`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


/-- One-layer grey atmosphere: if `eps > 0`, the atmosphere equilibrium
`2*eps*sigma*Ta^4 = eps*sigma*Ts^4` gives `Ta^4 = Ts^4 / 2`. -/
theorem atmosphere_temperature {eps σ Ts Ta : ℝ} (hσ : 0 < σ) (heps : 0 < eps)
    (h : 2 * eps * σ * Ta ^ 4 = eps * σ * Ts ^ 4) :
    Ta ^ 4 = Ts ^ 4 / 2 := by
  have hne : eps * σ ≠ 0 := mul_ne_zero (ne_of_gt heps) (ne_of_gt hσ)
  have h2 : eps * σ * (2 * Ta ^ 4) = eps * σ * (Ts ^ 4) := by
    linear_combination h
  have h3 : 2 * Ta ^ 4 = Ts ^ 4 := mul_left_cancel₀ hne h2
  linarith

/-- One-layer grey atmosphere: surface/atmosphere balances yield
`Ts^4 = Te^4 / (1 - eps/2)` for `eps ∈ [0,1]`. The top-of-atmosphere
balance is `sigma*Te^4 = (1-eps)*sigma*Ts^4 + eps*sigma*Ta^4`. -/
theorem surface_temperature {eps σ Te Ts Ta : ℝ} (hσ : 0 < σ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hatm : 2 * eps * σ * Ta ^ 4 = eps * σ * Ts ^ 4)
    (htoa : σ * Te ^ 4 = (1 - eps) * σ * Ts ^ 4 + eps * σ * Ta ^ 4) :
    Ts ^ 4 = Te ^ 4 / (1 - eps / 2) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  by_cases heq : eps = 0
  · subst heq
    simp only [sub_zero, one_mul, zero_mul, add_zero] at htoa
    simp only [zero_div, sub_zero, div_one]
    exact (mul_left_cancel₀ hσne htoa).symm
  · have heps : 0 < eps := heps0.lt_of_ne (Ne.symm heq)
    have hTa : Ta ^ 4 = Ts ^ 4 / 2 :=
      atmosphere_temperature hσ heps hatm
    have hpos : (0 : ℝ) < 1 - eps / 2 := by linarith
    have hdenom : (1 : ℝ) - eps / 2 ≠ 0 := ne_of_gt hpos
    have hTe : Te ^ 4 = Ts ^ 4 * (1 - eps / 2) := by
      have hσTe : σ * Te ^ 4 = σ * (Ts ^ 4 * (1 - eps / 2)) := by
        rw [htoa, hTa]
        ring
      exact mul_left_cancel₀ hσne hσTe
    rw [eq_div_iff hdenom]
    exact hTe.symm

/-- Transparent limit `eps = 0`: the surface temperature equals the
effective temperature, `Ts^4 = Te^4`. -/
theorem transparent_limit {σ Te Ts Ta : ℝ} (hσ : 0 < σ)
    (htoa : σ * Te ^ 4 = (1 - (0 : ℝ)) * σ * Ts ^ 4 + (0 : ℝ) * σ * Ta ^ 4) :
    Ts ^ 4 = Te ^ 4 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  simp only [sub_zero, one_mul, zero_mul, add_zero] at htoa
  exact (mul_left_cancel₀ hσne htoa).symm

/-- Non-vacuous witness: `eps = 1` gives `Ts^4 = 2 * Te^4`. -/
theorem opaque_witness {Te Ts : ℝ}
    (h : Ts ^ 4 = Te ^ 4 / (1 - (1 : ℝ) / 2)) :
    Ts ^ 4 = 2 * Te ^ 4 := by
  norm_num at h
  linarith


end EarthScience
