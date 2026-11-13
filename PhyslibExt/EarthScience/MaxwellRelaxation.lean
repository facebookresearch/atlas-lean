/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Tactic.FieldSimp
import PhyslibExt.EarthScience.FirstOrderKinetics

/-!
# Rheology: Maxwell relaxation

A Maxwell element under fixed total strain obeys `σ' = -(μ / η) * σ`,
hence `σ(t) = σ₀ * exp (-μ * t / η)`.

## i. Overview

`μ` is the elastic modulus, `η` the viscosity, `σ₀` the initial stress,
`t ≥ 0` the time. The elastic and viscous elements act in series under
fixed total strain, so the stress relaxes exponentially with relaxation
time `η / μ`: after one relaxation time the stress is `σ₀ / e`. No creep
law is claimed outside its model regime. The relaxation is first-order
decay with rate `k = μ / η`, so its derivative and initial value are
corollaries of `PhyslibExt.EarthScience.FirstOrderKinetics`; only the
nonnegativity and relaxation-time algebra are Maxwell-specific.

## ii. Key results

- `EarthScience.hasDerivAt_maxwell_relaxation`: the exponential obeys the
  Maxwell ODE.
- `EarthScience.maxwell_relaxation_initial_nonneg`: initial value and
  nonnegativity for `σ₀ ≥ 0`.
- `EarthScience.maxwell_relaxation_at_relaxation_time`: `σ(η / μ) = σ₀ / e`.

## iii. Table of contents

- A. Maxwell relaxation

## iv. References

- `EarthScience.firstOrder_decay_hasDerivAt` and
  `EarthScience.firstOrder_decay_initial` in
  `PhyslibExt.EarthScience.FirstOrderKinetics`.
- `Real.exp_neg` in Mathlib.

## A. Maxwell relaxation
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Maxwell relaxation: `σ(t) = σ₀ * exp (-(μ / η) * t)` obeys
`σ' = -(μ / η) * σ`. This is `EarthScience.firstOrder_decay_hasDerivAt`
with rate `k = μ / η`, which holds for all real parameters; `0 < μ` and
`0 < η` only restrict it to the physical Maxwell regime. -/
theorem hasDerivAt_maxwell_relaxation {μ η σ₀ t : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    HasDerivAt (fun t => σ₀ * Real.exp (-(μ / η) * t))
      (-(μ / η) * (σ₀ * Real.exp (-(μ / η) * t))) t :=
  firstOrder_decay_hasDerivAt (μ / η) σ₀ t

/-- Maxwell relaxation: initial value and nonnegativity for `σ₀ ≥ 0`.
The initial value is `EarthScience.firstOrder_decay_initial` with rate
`k = μ / η`. -/
theorem maxwell_relaxation_initial_nonneg {μ η σ₀ t : ℝ} (hσ₀ : 0 ≤ σ₀) :
    σ₀ * Real.exp (-(μ / η) * 0) = σ₀ ∧
      0 ≤ σ₀ * Real.exp (-(μ / η) * t) :=
  ⟨firstOrder_decay_initial (μ / η) σ₀, mul_nonneg hσ₀ (Real.exp_nonneg _)⟩

/-- Maxwell relaxation at one relaxation time `η / μ`: `σ = σ₀ / e`. -/
theorem maxwell_relaxation_at_relaxation_time {μ η σ₀ : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    σ₀ * Real.exp (-(μ / η) * (η / μ)) = σ₀ / Real.exp 1 := by
  have hμ' : μ ≠ 0 := ne_of_gt hμ
  have hη' : η ≠ 0 := ne_of_gt hη
  have h : -(μ / η) * (η / μ) = -1 := by
    field_simp
  rw [h, Real.exp_neg, div_eq_mul_inv]

end EarthScience
