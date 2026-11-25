/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Unit changes in a dynamic species balance

An amount conversion multiplies the amount by `α`. If old time is `τ` times new
time, all amount-per-time rates are multiplied by `α * τ` at the corresponding
time. Differentiation within the time set handles both open and closed intervals.
-/

namespace Domains.Chemistry.ProcessBalances.SpeciesBalanceScaling

private theorem scale_deriv {I : Set ℝ} {f : ℝ → ℝ} {α τ s d : ℝ}
    (h : HasDerivWithinAt f d I (τ * s)) :
    HasDerivWithinAt (fun u => α * f (τ * u)) (α * (d * τ)) {u | τ * u ∈ I} s := by
  have hid : HasDerivWithinAt (fun u : ℝ => u) 1 {u | τ * u ∈ I} s :=
    hasDerivWithinAt_id s _
  have htime : HasDerivWithinAt (fun u : ℝ => τ * u) τ {u | τ * u ∈ I} s := by
    simpa only [mul_one] using hid.const_mul τ
  exact (h.comp s htime (fun _ hu => hu)).const_mul α

/-- A componentwise species balance on `I` is equivalent to the rescaled balance on
`{s | τ * s ∈ I}`. The forward direction is the chain rule and the reverse uses
the inverse conversions. The same identity applies to mass instead of amount.

Source for the species balance: Rawlings and Ekerdt, *Chemical Reactor Analysis and
Design Fundamentals*, 2nd ed., seventh printing, §4.3, Equation 4.36 (p. 127). -/
public theorem species_balance_scaling_iff {S : Type*} (I : Set ℝ)
    (n inflow outflow generation : S → ℝ → ℝ) (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ) :
    (∀ i t, t ∈ I →
      HasDerivWithinAt (n i) (inflow i t - outflow i t + generation i t) I t) ↔
    (∀ i s, τ * s ∈ I →
      HasDerivWithinAt (fun u => α * n i (τ * u))
        ((α * τ) * inflow i (τ * s) - (α * τ) * outflow i (τ * s) +
          (α * τ) * generation i (τ * s)) {u | τ * u ∈ I} s) := by
  have hrate (x y z : ℝ) :
      α * ((x - y + z) * τ) = (α * τ) * x - (α * τ) * y + (α * τ) * z := by ring
  constructor
  · intro h i s hs
    simpa only [hrate] using scale_deriv (α := α) (h i (τ * s) hs)
  · intro h i t ht
    have htime (u : ℝ) : τ * (τ⁻¹ * u) = u := by
      rw [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]
    have hs : τ * (τ⁻¹ * t) ∈ I := by rwa [htime]
    have hset : {u | τ⁻¹ * u ∈ {v | τ * v ∈ I}} = I := by
      ext u
      change τ * (τ⁻¹ * u) ∈ I ↔ u ∈ I
      rw [htime]
    have hamount : (fun u => α⁻¹ * (α * n i (τ * (τ⁻¹ * u)))) = n i := by
      funext u
      rw [htime, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
    have hinverse (x y z : ℝ) :
        α⁻¹ * (((α * τ) * x - (α * τ) * y + (α * τ) * z) * τ⁻¹) = x - y + z := by
      rw [← hrate]
      calc
        _ = ((α⁻¹ * α) * (τ * τ⁻¹)) * (x - y + z) := by ring
        _ = x - y + z := by simp [hα.ne', hτ.ne']
    have hd := scale_deriv (α := α⁻¹) (h i (τ⁻¹ * t) hs)
    rw [hset, hamount, htime t, hinverse] at hd
    exact hd

end Domains.Chemistry.ProcessBalances.SpeciesBalanceScaling
