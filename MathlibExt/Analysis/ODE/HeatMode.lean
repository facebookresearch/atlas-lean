/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Single-mode heat-equation solution

The exact smooth single mode `u(t, x) = exp(-κ π² t) sin(π x)` satisfies
the heat equation `u_t = κ u_xx` on the nondimensionalized interval
`[0, 1]`, with Dirichlet boundary values `u(t, 0) = u(t, 1) = 0` and
initial data `u(0, x) = sin(π x)`.

## i. Overview

At fixed `x`, the `t`-derivative is `-κ π² u`; at fixed `t`, the second
`x`-derivative is `-π² u`; hence `u_t = κ u_xx`. The boundary values
use `sin 0 = 0` and `sin π = 0`; the initial value uses `exp 0 = 1`.
This is an exact single mode, not arbitrary-data well-posedness: no
general solution expansion or well-posedness is claimed, and the
physical length scale is restored by rescaling `x` explicitly.

## ii. Key results

- `EarthScience.heat_mode_hasDerivAt_t`: the `t`-derivative as a
  `HasDerivAt` statement.
- `EarthScience.heat_mode_satisfies_heat_eq`: `u_t = κ u_xx`, with
  `u_t` as `deriv` of the `t`-slice and `u_xx` as `iteratedDeriv 2`
  of the `x`-slice.
- `EarthScience.heat_mode_boundary_initial`: boundary and initial data.

## iii. Table of contents

- A. Time derivative
- B. Heat equation
- C. Boundary and initial data

## iv. References

- `HasDerivAt.exp`, `HasDerivAt.sin`, `HasDerivAt.cos` (Mathlib).

## A. Time derivative
-/

@[expose] public section

namespace EarthScience

/-- Time derivative of the single heat mode
`u(t, x) = exp(-κ π² t) sin(π x)` at fixed `x`. -/
theorem heat_mode_hasDerivAt_t {κ x t : ℝ} :
    HasDerivAt (fun t => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x))
      (-κ * Real.pi ^ 2 * Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) t := by
  have hlin : HasDerivAt (fun t : ℝ => -κ * Real.pi ^ 2 * t) (-κ * Real.pi ^ 2) t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul (-κ * Real.pi ^ 2)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-κ * Real.pi ^ 2 * t))
      (Real.exp (-κ * Real.pi ^ 2 * t) * (-κ * Real.pi ^ 2)) t :=
    HasDerivAt.exp hlin
  have hmul := HasDerivAt.mul_const hexp (Real.sin (Real.pi * x))
  convert hmul using 1
  ring

/-! ## B. Heat equation -/

/-- The single heat mode satisfies the heat equation `u_t = κ u_xx`,
with `u_t` as the `deriv` of the `t`-slice and `u_xx` as the second
`iteratedDeriv` of the `x`-slice. -/
theorem heat_mode_satisfies_heat_eq {κ t x : ℝ} :
    deriv (fun t => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) t
      = κ * iteratedDeriv 2
          (fun x => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) x := by
  have ht : deriv (fun t => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) t
      = -κ * Real.pi ^ 2 * Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x) :=
    heat_mode_hasDerivAt_t.deriv
  have hlin_x : ∀ x0 : ℝ, HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi x0 := fun x0 => by
    simpa only [mul_one, id_eq] using (hasDerivAt_id x0).const_mul Real.pi
  have h1 : ∀ x0 : ℝ, HasDerivAt
      (fun x : ℝ => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x))
      (Real.exp (-κ * Real.pi ^ 2 * t) * (Real.cos (Real.pi * x0) * Real.pi)) x0 := fun x0 => by
    have hsin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x))
        (Real.cos (Real.pi * x0) * Real.pi) x0 :=
      HasDerivAt.sin (hlin_x x0)
    exact hsin.const_mul (Real.exp (-κ * Real.pi ^ 2 * t))
  have d1_eq : deriv (fun x : ℝ => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x))
      = (fun x : ℝ => Real.exp (-κ * Real.pi ^ 2 * t) * (Real.cos (Real.pi * x) * Real.pi)) :=
    funext fun x0 => (h1 x0).deriv
  have h2 : ∀ x0 : ℝ, HasDerivAt
      (fun x : ℝ => Real.exp (-κ * Real.pi ^ 2 * t) * (Real.cos (Real.pi * x) * Real.pi))
      (Real.exp (-κ * Real.pi ^ 2 * t) * ((-Real.sin (Real.pi * x0) * Real.pi) * Real.pi)) x0 :=
    fun x0 => by
      have hcos : HasDerivAt (fun x : ℝ => Real.cos (Real.pi * x))
          (-Real.sin (Real.pi * x0) * Real.pi) x0 :=
        HasDerivAt.cos (hlin_x x0)
      have hcos_mul : HasDerivAt (fun x : ℝ => Real.cos (Real.pi * x) * Real.pi)
          ((-Real.sin (Real.pi * x0) * Real.pi) * Real.pi) x0 :=
        HasDerivAt.mul_const hcos Real.pi
      exact hcos_mul.const_mul (Real.exp (-κ * Real.pi ^ 2 * t))
  have h_it : iteratedDeriv 2
        (fun x : ℝ => Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) x
      = Real.exp (-κ * Real.pi ^ 2 * t) * ((-Real.sin (Real.pi * x) * Real.pi) * Real.pi) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, d1_eq]
    exact (h2 x).deriv
  rw [ht, h_it]
  ring

/-! ## C. Boundary and initial data -/

/-- Boundary and initial data of the single heat mode: `u(t, 0) = 0`,
`u(t, 1) = 0`, and `u(0, x) = sin(π x)`. -/
theorem heat_mode_boundary_initial {κ t x : ℝ} :
    Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * 0) = 0 ∧
    Real.exp (-κ * Real.pi ^ 2 * t) * Real.sin (Real.pi * 1) = 0 ∧
    Real.exp (-κ * Real.pi ^ 2 * 0) * Real.sin (Real.pi * x) = Real.sin (Real.pi * x) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp [Real.sin_pi]
  · simp

end EarthScience
