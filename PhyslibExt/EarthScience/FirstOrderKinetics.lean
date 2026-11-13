/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Biology.Biophysics.CompartmentKinetics
/-!
# First-order decay and its integrated consumption

For real parameters `k` and `c0`, `c(t) = c0 * exp(-k*t)` solves
`c' = -k*c`, starts at `c0`, and satisfies the signed balance identity
`∫ s in 0..t, k*c(s) = c0 - c(t)`. These unrestricted identities are
algebraic extensions: their interpretation as a nonnegative, nonincreasing
concentration and nonnegative consumption requires `0 ≤ k`, `0 ≤ c0`,
and `0 ≤ t`. A negative `k` instead permits exponential growth.
These are corollaries of the compartment model
`MathlibExt.Biology.Biophysics.CompartmentKinetics.amount` at infusion rate
`R = 0`: `amount_bolus` identifies `amount k 0 c0 t` with this exponential,
`hasDerivAt_amount` supplies the derivative, and `amount_zero` the initial
value. The consumption identity is proved from `hasDerivAt_amount` by the
fundamental theorem of calculus, so it holds for every `t`, including
negative `t` (signed integral); the compartment mass balance
`amount_add_eliminated` gives the same identity for nonnegative time.
The physical interpretation additionally requires `0 ≤ k` and `0 ≤ c0`.

## i. Overview

Closed, well-mixed, constant-volume first-order reaction with initial
concentration `c0`. No transport-limited or reversible claim is made, and
the source of a fitted `k` is empirical metadata, outside this file.

## ii. Key results

- `EarthScience.firstOrder_decay_hasDerivAt`: `c(t) = c0*exp(-k*t)`
  satisfies `c' = -k*c`.
- `EarthScience.firstOrder_decay_initial`: `c(0) = c0`.
- `EarthScience.firstOrder_decay_consumption`: `∫ s in 0..t, k*c(s) = c0 - c(t)`.

## iii. References

- `MathlibExt.Biology.Biophysics.CompartmentKinetics` (`amount_bolus`,
  `hasDerivAt_amount`, `amount_zero`, `amount_add_eliminated`): the
  compartment model these theorems are corollaries of.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` for the consumption integral.
-/

@[expose] public section

namespace EarthScience

open MathlibExt.Biology.Biophysics.CompartmentKinetics

/-- The exponential profile solves `c' = -k*c` for arbitrary real parameters.
It describes nonnegative decay for `0 ≤ k` and `0 ≤ c0`.
This is `hasDerivAt_amount` at infusion rate `R = 0`, with the amount
identified with the exponential by `amount_bolus`. -/
theorem firstOrder_decay_hasDerivAt (k c0 t : ℝ) :
    HasDerivAt (fun t => c0 * Real.exp (-k * t))
      (-k * (c0 * Real.exp (-k * t))) t := by
  have h := hasDerivAt_amount k 0 c0 t
  rw [show (fun t => c0 * Real.exp (-k * t)) = amount k 0 c0 from
    funext fun s => (amount_bolus k c0 s).symm]
  convert h using 1
  rw [amount_bolus]
  ring

/-- First-order decay starts at `c0`: `amount_zero` at `R = 0`, with the
amount identified with the exponential by `amount_bolus`. -/
theorem firstOrder_decay_initial (k c0 : ℝ) :
    c0 * Real.exp (-k * 0) = c0 := by
  rw [← amount_bolus k c0 0]
  exact amount_zero k 0 c0

/-- The signed integrated balance over `0..t` is `c0 - c(t)`.
It represents nonnegative consumption when `0 ≤ k`, `0 ≤ c0`, and `0 ≤ t`.
Proved from `hasDerivAt_amount` at `R = 0` by the fundamental theorem of
calculus, so it holds for every `t`; for `0 ≤ t` it is also the compartment
mass balance `amount_add_eliminated` at `R = 0` rewritten by `amount_bolus`. -/
theorem firstOrder_decay_consumption (k c0 t : ℝ) :
    ∫ s in (0 : ℝ)..t, k * (c0 * Real.exp (-k * s)) =
      c0 - c0 * Real.exp (-k * t) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => -(amount k 0 c0 s)) (k * (amount k 0 c0 x)) x := by
    intro x _
    exact ((hasDerivAt_amount k 0 c0 x).neg).congr_deriv (by ring)
  have hcont : Continuous (fun s : ℝ => k * (amount k 0 c0 s)) :=
    (continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_amount k 0 c0 s).continuousAt).const_mul k
  have hint : IntervalIntegrable (fun s : ℝ => k * (amount k 0 c0 s))
      MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [← amount_bolus, amount_zero] at hFTC ⊢
  rw [hFTC]
  ring

end EarthScience
