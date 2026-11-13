/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.Ring

/-!
# Energy conservation for an undamped oscillator

For the undamped oscillator `x'' = -ω₀ ^ 2 * x`, the energy
`E(t) = (x'(t)) ^ 2 / 2 + ω₀ ^ 2 * (x(t)) ^ 2 / 2` has derivative `0`,
so it is conserved. For the harmonic motion `x(t) = A * cos (ω₀ * t)`
the energy is `(ω₀ ^ 2 * A ^ 2) / 2` at every `t`.

## i. Overview

The derivative of `E` is computed from the `HasDerivAt` data for `x`
and `x'`; conservation follows because a function with zero derivative
everywhere is constant.

## ii. Key results

- `EarthScience.oscillator_energy_hasDerivAt`: `E` has derivative `0`.
- `EarthScience.oscillator_energy_const`: `E` is the same at any two times.
- `EarthScience.oscillator_energy_harmonic`: energy of harmonic motion.

## iii. Table of contents

- A. Energy derivative and conservation
- B. Harmonic motion

## iv. References

- `HasDerivAt.fun_pow` / `HasDerivAt.div_const` in Mathlib.
- `Convex.norm_image_sub_le_of_norm_deriv_le` in Mathlib.
- `Real.sin_sq_add_cos_sq` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Energy of an undamped oscillator: `E t = (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2`.
If `x` satisfies `x'' = -ω₀ ^ 2 * x` (as `HasDerivAt` data at `t`), then
`E` has derivative `0` at `t`. -/
theorem oscillator_energy_hasDerivAt {x : ℝ → ℝ} {ω₀ t : ℝ}
    (hx : HasDerivAt x (deriv x t) t)
    (hx' : HasDerivAt (deriv x) (-ω₀ ^ 2 * x t) t) :
    HasDerivAt (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) 0 t := by
  have h1 : HasDerivAt (fun i => (deriv x i) ^ 2)
      ((2 : ℝ) * (deriv x t) ^ (2 - 1) * (-ω₀ ^ 2 * x t)) t :=
    hx'.fun_pow 2
  have h1d : HasDerivAt (fun i => (deriv x i) ^ 2 / 2)
      (((2 : ℝ) * (deriv x t) ^ (2 - 1) * (-ω₀ ^ 2 * x t)) / 2) t :=
    h1.div_const 2
  have h2 : HasDerivAt (fun i => (x i) ^ 2)
      ((2 : ℝ) * (x t) ^ (2 - 1) * (deriv x t)) t :=
    hx.fun_pow 2
  have h2c : HasDerivAt (fun i => ω₀ ^ 2 * (x i) ^ 2)
      (ω₀ ^ 2 * ((2 : ℝ) * (x t) ^ (2 - 1) * (deriv x t))) t :=
    h2.const_mul (ω₀ ^ 2)
  have h2d : HasDerivAt (fun i => ω₀ ^ 2 * (x i) ^ 2 / 2)
      ((ω₀ ^ 2 * ((2 : ℝ) * (x t) ^ (2 - 1) * (deriv x t))) / 2) t :=
    h2c.div_const 2
  have hsum := h1d.add h2d
  have heq : (((2 : ℝ) * (deriv x t) ^ (2 - 1) * (-ω₀ ^ 2 * x t)) / 2) +
      ((ω₀ ^ 2 * ((2 : ℝ) * (x t) ^ (2 - 1) * (deriv x t))) / 2) = 0 := by
    simp
    ring
  have hfun : ((fun i => (deriv x i) ^ 2 / 2) + (fun i => ω₀ ^ 2 * (x i) ^ 2 / 2)) =
      (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) := rfl
  rw [hfun, heq] at hsum
  exact hsum

/-- Conservation: under the oscillator equation at every `t`, the energy
is the same at any two times. -/
theorem oscillator_energy_const {x : ℝ → ℝ} {ω₀ : ℝ}
    (hx : ∀ t, HasDerivAt x (deriv x t) t)
    (hx' : ∀ t, HasDerivAt (deriv x) (-ω₀ ^ 2 * x t) t) :
    ∀ t₁ t₂, (deriv x t₁) ^ 2 / 2 + ω₀ ^ 2 * (x t₁) ^ 2 / 2 =
      (deriv x t₂) ^ 2 / 2 + ω₀ ^ 2 * (x t₂) ^ 2 / 2 := by
  intro t₁ t₂
  have hE : ∀ t, HasDerivAt (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) 0 t :=
    fun t => oscillator_energy_hasDerivAt (hx t) (hx' t)
  have hdiff : ∀ x_1 ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) x_1 :=
    fun x_1 _ => (hE x_1).differentiableAt
  have hbound : ∀ x_1 ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) x_1‖ ≤ (0 : ℝ) := by
    intro x_1 _
    rw [(hE x_1).deriv]
    simp
  have hle := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (Set.mem_univ t₂) (Set.mem_univ t₁)
  simp only [zero_mul, norm_le_zero_iff] at hle
  exact sub_eq_zero.mp hle

/-- Harmonic oscillator: for `x t = A * cos (ω₀ * t)` the energy is
`(ω₀ ^ 2 * A ^ 2) / 2` at every `t`. -/
theorem oscillator_energy_harmonic {A ω₀ t : ℝ} :
    (deriv (fun t => A * Real.cos (ω₀ * t)) t) ^ 2 / 2 +
      ω₀ ^ 2 * ((fun t => A * Real.cos (ω₀ * t)) t) ^ 2 / 2 =
      ω₀ ^ 2 * A ^ 2 / 2 := by
  have hlin : HasDerivAt (fun t => ω₀ * t) ω₀ t := by
    simpa using (hasDerivAt_id t).const_mul ω₀
  have hcos : HasDerivAt (fun t => Real.cos (ω₀ * t)) (-Real.sin (ω₀ * t) * ω₀) t :=
    hlin.cos
  have hfull : HasDerivAt (fun t => A * Real.cos (ω₀ * t)) (A * (-Real.sin (ω₀ * t) * ω₀)) t :=
    hcos.const_mul A
  have hderiv : deriv (fun t => A * Real.cos (ω₀ * t)) t = A * (-Real.sin (ω₀ * t) * ω₀) :=
    hfull.deriv
  rw [hderiv]
  simp only []
  have htrig := Real.sin_sq_add_cos_sq (ω₀ * t)
  calc (A * (-Real.sin (ω₀ * t) * ω₀)) ^ 2 / 2 + ω₀ ^ 2 * (A * Real.cos (ω₀ * t)) ^ 2 / 2
      = ω₀ ^ 2 * A ^ 2 * (Real.sin (ω₀ * t) ^ 2 + Real.cos (ω₀ * t) ^ 2) / 2 := by ring
    _ = ω₀ ^ 2 * A ^ 2 / 2 := by rw [htrig]; ring
end EarthScience
