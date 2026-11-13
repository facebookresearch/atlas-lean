/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Remote-sensing observation operators

## i. Overview

For `I' = -kappa(s)*I + j(s)` with continuous `kappa, j`, the
integrating-factor identity gives the explicit Duhamel form
`I(L) = I0*exp(-∫_0^L kappa) + ∫_0^L j(s)*exp(-∫_s^L kappa) ds`.
With fixed `kappa` and a finite basis `j = ∑ a_i * b_i`, this is affine
in `a`: `I(L) = I0*exp(-∫_0^L kappa) + ∑ a_i * w_i` with weights
`w_i = ∫_0^L b_i(s)*exp(-∫_s^L kappa) ds`. No scattering is assumed;
Gaussian inverse results apply only to this linearized,
fixed-absorption operator.

## ii. Key results

- `EarthScience.RadiativeTransfer.integrating_factor`: `mu(L)*I(L) = I0 + ∫ mu*j`,
  `mu(s) = exp(∫_0^s kappa)`.
- `EarthScience.RadiativeTransfer.explicit_form`: the Duhamel form for `I(L)`.
- `EarthScience.RadiativeTransfer.finite_basis`: affine observation operator in the basis
  coefficients.
- `EarthScience.RadiativeTransfer.witness`: `kappa = 1, j = 0, I0 = 1` gives `I(L) = exp(-L)`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience.RadiativeTransfer


open MeasureTheory Set intervalIntegral

/-- FTC-1 for the integrating factor: the primitive of a continuous `κ`
has derivative `κ s` at every `s`. -/
private theorem primitive_hasDerivAt (κ : ℝ → ℝ) (hκ : Continuous κ) (s : ℝ) :
    HasDerivAt (fun u => ∫ x in (0:ℝ)..u, κ x) (κ s) s :=
  intervalIntegral.integral_hasDerivAt_right (hκ.intervalIntegrable 0 s)
    (hκ.stronglyMeasurableAtFilter volume (nhds s)) hκ.continuousAt

/-- The integrating factor `μ` has derivative `μ s * κ s` at every `s`. -/
private theorem mu_hasDerivAt (κ : ℝ → ℝ) (hκ : Continuous κ) (s : ℝ) :
    HasDerivAt (fun s => Real.exp (∫ x in (0:ℝ)..s, κ x))
      (Real.exp (∫ x in (0:ℝ)..s, κ x) * κ s) s :=
  (primitive_hasDerivAt κ hκ s).exp

/-- Product rule: `(μ * I)' = μ * j` along a solution of the ODE. -/
private theorem weighted_hasDerivAt (κ j I : ℝ → ℝ) (hκ : Continuous κ)
    (hODE : ∀ t : ℝ, HasDerivAt I (-κ t * I t + j t) t) (s : ℝ) :
    HasDerivAt (fun s => Real.exp (∫ x in (0:ℝ)..s, κ x) * I s)
      (Real.exp (∫ x in (0:ℝ)..s, κ x) * j s) s := by
  have h := (mu_hasDerivAt κ hκ s).mul (hODE s)
  have heq : (Real.exp (∫ x in (0:ℝ)..s, κ x) * κ s) * I s
      + Real.exp (∫ x in (0:ℝ)..s, κ x) * (-κ s * I s + j s)
      = Real.exp (∫ x in (0:ℝ)..s, κ x) * j s := by ring
  rw [← heq]
  exact h

set_option linter.unusedVariables false in
/-- Integrating-factor identity for `I' = -kappa*I + j`: with
`mu(s) = exp(∫ x in 0..s, kappa x)`, the weighted endpoint satisfies
`mu(L) * I(L) = I0 + ∫ s in 0..L, mu(s) * j(s)`. -/
theorem integrating_factor {κ j I : ℝ → ℝ} {L I0 : ℝ} (hL : 0 ≤ L)
    (hκ : Continuous κ) (hj : Continuous j)
    (hODE : ∀ t : ℝ, HasDerivAt I (-κ t * I t + j t) t)
    (hI0 : I 0 = I0) :
    Real.exp (∫ x in (0:ℝ)..L, κ x) * I L
      = I0 + ∫ s in (0:ℝ)..L, Real.exp (∫ x in (0:ℝ)..s, κ x) * j s := by
  have hμcont : Continuous fun s => Real.exp (∫ x in (0:ℝ)..s, κ x) :=
    continuous_iff_continuousAt.mpr fun s => (mu_hasDerivAt κ hκ s).continuousAt
  have hint : IntervalIntegrable
      (fun s => Real.exp (∫ x in (0:ℝ)..s, κ x) * j s) volume 0 L :=
    (hμcont.mul hj).intervalIntegrable 0 L
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := L)
    (f := fun s => Real.exp (∫ x in (0:ℝ)..s, κ x) * I s)
    (f' := fun s => Real.exp (∫ x in (0:ℝ)..s, κ x) * j s)
    (fun x _ => weighted_hasDerivAt κ j I hκ hODE x)
    hint
  have hFTC2 : (∫ s in (0:ℝ)..L, Real.exp (∫ x in (0:ℝ)..s, κ x) * j s)
      = Real.exp (∫ x in (0:ℝ)..L, κ x) * I L
        - Real.exp (∫ x in (0:ℝ)..(0:ℝ), κ x) * I 0 := hFTC
  have h0 : Real.exp (∫ x in (0:ℝ)..(0:ℝ), κ x) = 1 := by
    rw [intervalIntegral.integral_same]
    exact Real.exp_zero
  rw [h0, hI0] at hFTC2
  linarith

/-- Explicit Duhamel form: dividing the integrating-factor identity by
`mu(L)` and using `∫ x in 0..L, kappa = ∫ x in 0..s + ∫ x in s..L`,
`I(L) = I0*exp(-∫_0^L kappa) + ∫_0^L j(s)*exp(-∫_s^L kappa) ds`. -/
theorem explicit_form {κ j I : ℝ → ℝ} {L I0 : ℝ} (hL : 0 ≤ L)
    (hκ : Continuous κ) (hj : Continuous j)
    (hODE : ∀ t : ℝ, HasDerivAt I (-κ t * I t + j t) t)
    (hI0 : I 0 = I0) :
    I L = I0 * Real.exp (-∫ x in (0:ℝ)..L, κ x)
      + ∫ s in (0:ℝ)..L, j s * Real.exp (-∫ x in s..L, κ x) := by
  have hIF := integrating_factor hL hκ hj hODE hI0
  have hsplit : ∀ s : ℝ, (∫ x in (0:ℝ)..L, κ x)
      = (∫ x in (0:ℝ)..s, κ x) + ∫ x in s..L, κ x := by
    intro s
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hκ.intervalIntegrable 0 s) (hκ.intervalIntegrable s L)).symm
  have hinter : ∀ s : ℝ, Real.exp (∫ x in (0:ℝ)..s, κ x) * j s
      = Real.exp (∫ x in (0:ℝ)..L, κ x)
        * (j s * Real.exp (-∫ x in s..L, κ x)) := by
    intro s
    have hexp : Real.exp (∫ x in (0:ℝ)..s, κ x)
        = Real.exp (∫ x in (0:ℝ)..L, κ x) * Real.exp (-∫ x in s..L, κ x) := by
      have harg : (∫ x in (0:ℝ)..L, κ x) + (-∫ x in s..L, κ x)
          = ∫ x in (0:ℝ)..s, κ x := by
        rw [hsplit s]
        ring
      rw [← Real.exp_add, harg]
    rw [hexp]
    ring
  have hINT : (∫ s in (0:ℝ)..L, Real.exp (∫ x in (0:ℝ)..s, κ x) * j s)
      = Real.exp (∫ x in (0:ℝ)..L, κ x)
        * (∫ s in (0:ℝ)..L, j s * Real.exp (-∫ x in s..L, κ x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    exact hinter x
  rw [hINT] at hIF
  have hμL : Real.exp (∫ x in (0:ℝ)..L, κ x) ≠ 0 := Real.exp_ne_zero _
  have hexp0 : Real.exp (-∫ x in (0:ℝ)..L, κ x)
      = (Real.exp (∫ x in (0:ℝ)..L, κ x))⁻¹ := Real.exp_neg _
  rw [hexp0]
  apply mul_right_cancel₀ hμL
  rw [add_mul, mul_assoc, inv_mul_cancel₀ hμL, mul_one]
  linear_combination hIF

/-- Finite-basis affine observation operator: if `j = ∑ i in s, a i * b i`,
then `I(L) = I0*exp(-∫_0^L kappa) + ∑ i in s, a i * w i` where
`w i = ∫_0^L b i(s)*exp(-∫_s^L kappa) ds`. -/
theorem finite_basis {κ : ℝ → ℝ} {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (b : ι → ℝ → ℝ) {L I0 : ℝ} (hL : 0 ≤ L)
    (hκ : Continuous κ) (hb : ∀ i ∈ s, Continuous (b i))
    {I : ℝ → ℝ}
    (hODE : ∀ t : ℝ, HasDerivAt I (-κ t * I t + ∑ i ∈ s, a i * b i t) t)
    (hI0 : I 0 = I0) :
    I L = I0 * Real.exp (-∫ x in (0:ℝ)..L, κ x)
      + ∑ i ∈ s, a i * (∫ t in (0:ℝ)..L, b i t * Real.exp (-∫ x in t..L, κ x)) := by
  have hj : Continuous fun t => ∑ i ∈ s, a i * b i t :=
    continuous_finsetSum s fun i hi => continuous_const.mul (hb i hi)
  have hex := explicit_form (j := fun t => ∑ i ∈ s, a i * b i t)
    hL hκ hj hODE hI0
  have h1 : ∀ t : ℝ, (∑ i ∈ s, a i * b i t) * Real.exp (-∫ x in t..L, κ x)
      = ∑ i ∈ s, a i * (b i t * Real.exp (-∫ x in t..L, κ x)) := by
    intro t
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hKcont : Continuous fun t => ∫ x in (0:ℝ)..t, κ x :=
    continuous_iff_continuousAt.mpr
      fun t => (primitive_hasDerivAt κ hκ t).continuousAt
  have hK2 : Continuous fun t => ∫ x in t..L, κ x := by
    have hfun : (fun t => ∫ x in t..L, κ x)
        = fun t => (∫ x in (0:ℝ)..L, κ x) - ∫ x in (0:ℝ)..t, κ x := by
      funext t
      show (∫ x in t..L, κ x) = (∫ x in (0:ℝ)..L, κ x) - ∫ x in (0:ℝ)..t, κ x
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hκ.intervalIntegrable (μ := volume) 0 t)
        (hκ.intervalIntegrable (μ := volume) t L)
      linarith
    rw [hfun]
    exact continuous_const.sub hKcont
  have hw : Continuous fun t => Real.exp (-∫ x in t..L, κ x) :=
    Real.continuous_exp.comp hK2.neg
  have h2 : (∫ s_ in (0:ℝ)..L, (∑ i ∈ s, a i * b i s_) * Real.exp (-∫ x in s_..L, κ x))
      = ∑ i ∈ s, ∫ t in (0:ℝ)..L, a i * (b i t * Real.exp (-∫ x in t..L, κ x)) := by
    have hcongr :
        (∫ s_ in (0:ℝ)..L, (∑ i ∈ s, a i * b i s_) * Real.exp (-∫ x in s_..L, κ x))
          = ∫ s_ in (0:ℝ)..L, ∑ i ∈ s, a i * (b i s_ * Real.exp (-∫ x in s_..L, κ x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h1 x
    rw [hcongr]
    apply intervalIntegral.integral_finsetSum
    intro i hi
    exact ((continuous_const.mul ((hb i hi).mul hw)).intervalIntegrable 0 L)
  have hgoal : (∫ s_ in (0:ℝ)..L, (∑ i ∈ s, a i * b i s_) * Real.exp (-∫ x in s_..L, κ x))
      = ∑ i ∈ s, a i * (∫ t in (0:ℝ)..L, b i t * Real.exp (-∫ x in t..L, κ x)) := by
    rw [h2]
    apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_const_mul _ _
  rw [hex, add_left_cancel_iff]
  exact hgoal

/-- Witness `kappa = 1, j = 0, I0 = 1`: the explicit form gives
`I(L) = exp(-L)`. Stated as an integral evaluation plus the
explicit-form conclusion for a solution with zero source. -/
theorem witness {I : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hODE : ∀ t : ℝ, HasDerivAt I (-(1:ℝ) * I t + (0:ℝ)) t)
    (hI0 : I 0 = 1) :
    I L = Real.exp (-L) := by
  have hex := explicit_form (κ := fun _ => (1:ℝ)) (j := fun _ => (0:ℝ))
    hL continuous_const continuous_const hODE hI0
  have hex2 : I L = 1 * Real.exp (-∫ x in (0:ℝ)..L, (1:ℝ))
      + ∫ s in (0:ℝ)..L, (0:ℝ) * Real.exp (-∫ x in s..L, (1:ℝ)) := hex
  have hint1 : (∫ x in (0:ℝ)..L, (1:ℝ)) = L := by simp
  have hint0 : (∫ s in (0:ℝ)..L, (0:ℝ) * Real.exp (-∫ x in s..L, (1:ℝ))) = 0 := by
    simp only [zero_mul, intervalIntegral.integral_zero]
  rw [hint1, hint0, one_mul, add_zero] at hex2
  exact hex2



end EarthScience.RadiativeTransfer
