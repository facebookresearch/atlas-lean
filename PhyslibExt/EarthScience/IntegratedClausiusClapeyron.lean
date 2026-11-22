/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

open scoped Topology

/-!
# Integrated Clausius-Clapeyron relation

Along a coexistence curve, the Clapeyron relation in latent-heat form is
`dp / dT = L / (T * (v₂ - v₁))`. Under the ideal-vapor approximation the
vapour specific volume dominates, `v₂ - v₁ = R * T / p` (the liquid volume
is neglected and the vapour obeys the ideal-gas law), so
`dp / dT = L * p / (R * T ^ 2)`. For constant latent heat `L`, integrating
from `T₁` to `T₂` gives
`log (p₂ / p₁) = -(L / R) * (1 / T₂ - 1 / T₁)`. The companion module
`PhyslibExt.EarthScience.PhaseEquilibrium` proves the Clapeyron relation
itself; this module adds the ideal-vapor differential form and its integral.

## i. Overview

The integrated form is proved by applying the fundamental theorem of
calculus to `F(t) = log (p t) + (L / R) * t⁻¹`, whose derivative is `0`
on `[T₁, T₂]` under the differential form.

## ii. Key results

- `EarthScience.clausius_clapeyron_differential`: the ideal-vapor
  differential form.
- `EarthScience.integrated_clausius_clapeyron`: the integrated form.

## iii. Table of contents

- A. Ideal-vapor differential form
- B. Integrated form

## iv. References

- Donald A. McQuarrie and John D. Simon, *Physical Chemistry: A Molecular
  Approach* (University Science Books, 1997), Chapter 23, Phase Equilibria,
  Sections 23.3-23.4 (Clapeyron equation) and the Clausius-Clapeyron
  approximation for an ideal vapour.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Clausius-Clapeyron differential form under the ideal-vapor approximation:
if `dp / dT = L / (T * (v₂ - v₁))` (latent-heat Clapeyron form) and the vapour
specific volume dominates, `v₂ - v₁ = R * T / p`, then `dp / dT = L * p / (R * T ^ 2)`. -/
theorem clausius_clapeyron_differential {dp_dT L R T p v₂ v₁ : ℝ}
    (hT : T ≠ 0) (hp : p ≠ 0) (hR : R ≠ 0)
    (hclap : dp_dT = L / (T * (v₂ - v₁)))
    (hvapor : v₂ - v₁ = R * T / p) :
    dp_dT = L * p / (R * T ^ 2) := by
  rw [hvapor] at hclap
  rw [hclap]
  field_simp

/-- Integrated Clausius-Clapeyron: if `p` is differentiable on `[T₁, T₂]` with
`0 < T₁`, `p t > 0` there, and `p` satisfies the differential form
`HasDerivAt p (L * p t / (R * t ^ 2)) t` for every `t ∈ [T₁, T₂]`, with
constant latent heat `L` and `R > 0`, then
`log (p T₂ / p T₁) = -(L / R) * (1 / T₂ - 1 / T₁)`. The identity needs no sign
condition on `L`: zero and negative `L` are allowed. -/
theorem integrated_clausius_clapeyron {p : ℝ → ℝ} {T₁ T₂ L R : ℝ}
    (hT : 0 < T₁) (hTle : T₁ ≤ T₂) (hR : 0 < R)
    (hp : ∀ t ∈ Set.Icc T₁ T₂, 0 < p t)
    (hder : ∀ t ∈ Set.Icc T₁ T₂, HasDerivAt p (L * p t / (R * t ^ 2)) t) :
    Real.log (p T₂ / p T₁) = -(L / R) * (1 / T₂ - 1 / T₁) := by
  have hR' : R ≠ 0 := ne_of_gt hR
  have hT₁mem : T₁ ∈ Set.Icc T₁ T₂ := ⟨le_rfl, hTle⟩
  have hT₂mem : T₂ ∈ Set.Icc T₁ T₂ := ⟨hTle, le_rfl⟩
  have hp1 : p T₁ ≠ 0 := ne_of_gt (hp T₁ hT₁mem)
  have hp2 : p T₂ ≠ 0 := ne_of_gt (hp T₂ hT₂mem)
  have hderiv : ∀ t ∈ Set.uIcc T₁ T₂,
      HasDerivAt ((fun y => Real.log (p y)) + (fun y => (L / R) * y⁻¹))
        ((fun _ => (0 : ℝ)) t) t := by
    intro t ht
    rw [Set.uIcc_of_le hTle] at ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht.1
    have htn : t ≠ 0 := ne_of_gt htpos
    have hpt : p t ≠ 0 := ne_of_gt (hp t ht)
    have h1 := (hder t ht).log hpt
    have h2 := HasDerivAt.const_mul (L / R) (hasDerivAt_inv htn)
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 htn
    have hval : (L * p t / (R * t ^ 2)) / p t + (L / R) * (-(t ^ 2)⁻¹) = 0 := by
      field_simp
      ring
    have h := h1.add h2
    rw [hval] at h
    exact h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := (fun y => Real.log (p y)) + (fun y => (L / R) * y⁻¹))
    (f' := fun _ => (0 : ℝ)) hderiv intervalIntegrable_const
  have h0 : (∫ y in T₁..T₂, (fun _ => (0 : ℝ)) y) = 0 := by simp
  rw [h0] at hFTC
  simp only [Pi.add_apply] at hFTC
  have hFeq := hFTC.symm
  rw [Real.log_div hp2 hp1, one_div, one_div]
  linear_combination hFeq
end EarthScience
