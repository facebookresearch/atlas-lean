/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Kinetic energy of a particle: derivative is the power of the force

## i. Overview

For a particle of constant mass `m` whose velocity `v` has derivative
(acceleration) `a t` at time `t`, the kinetic energy
`K(t) = m * ‖v t‖ ^ 2 / 2` has derivative `inner (m • a t) (v t)`.
With `F = m • a`, this is the work-energy identity, conditional on
Newton's model. Mass is a mass, position a length, `K` an energy;
force is not acceleration.

## ii. Key results

- `EarthScience.hasDerivAt_kinetic_energy`: `K' = inner (m • a) v`.
- `EarthScience.kinetic_energy_nonneg`: `K ≥ 0` for `m ≥ 0`.

## iii. Table of contents

- A. Derivative of kinetic energy
- B. Nonnegativity

## iv. References

- `HasDerivAt.norm_sq` in Mathlib (derivative of the squared norm).
- `real_inner_smul_left` / `real_inner_comm` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Kinetic energy `K(t) = m * ‖v t‖ ^ 2 / 2` of a particle whose velocity
`v` has derivative (acceleration) `a t` at time `t` has derivative
`inner (m • a t) (v t)`. Here `v` plays the role of `r'`. -/
theorem hasDerivAt_kinetic_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m : ℝ} {v : ℝ → E} {a : ℝ → E} {t : ℝ}
    (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun t => m * ‖v t‖ ^ 2 / 2) (inner ℝ (m • a t) (v t)) t := by
  have h2 : HasDerivAt (fun x => ‖v x‖ ^ 2) (2 * inner ℝ (v t) (a t)) t :=
    hv.norm_sq
  have h3 := (h2.const_mul m).div_const 2
  have hder : m * (2 * inner ℝ (v t) (a t)) / 2 = inner ℝ (m • a t) (v t) := by
    rw [real_inner_smul_left, real_inner_comm (a t) (v t)]
    ring
  rw [hder] at h3
  exact h3

/-- Kinetic energy is nonnegative for nonnegative mass. -/
theorem kinetic_energy_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m : ℝ} (hm : 0 ≤ m) (v : E) :
    0 ≤ m * ‖v‖ ^ 2 / 2 := by
  positivity

end EarthScience
