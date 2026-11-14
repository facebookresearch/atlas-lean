/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Bernoulli along a streamline: fluid balances and model reductions

For steady incompressible inviscid flow satisfying the Euler balance
with a time-independent potential, the directional derivative of the
Bernoulli head `p / rho + ||u||^2 / 2 + Phi` along `u` is zero. This is
constancy along a streamline, not global constancy of the Bernoulli head.

## i. Overview

The kinetic-energy identity says the directional derivative of
`||u||^2 / 2` along `u x` is the inner product of `u x` with the
convective derivative `(fderiv u x) (u x)`. Combining it with the
pressure term and the potential term, the directional derivative of the
Bernoulli head is the Euler balance dotted with `u x`, which is zero by
hypothesis. Constant density `rho > 0`, conservative body force, steady
flow. No head loss, no unsteady surface-wave claim, and no claim that
the head is constant across distinct streamlines.

## ii. Key results

- `EarthScience.kinetic_directional_deriv`: directional derivative of
  kinetic energy per unit mass.
- `EarthScience.bernoulli_along_streamline`: Bernoulli head has zero
  directional derivative along `u x`.

## iii. Table of contents

- A. Kinetic-energy identity
- B. Bernoulli along a streamline

## iv. References

- `HasFDerivAt` API in Mathlib, including `HasFDerivAt.norm_sq`.
-/

@[expose] public section

namespace EarthScience

private theorem kinetic_hasFDerivAt (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) (hu : HasFDerivAt u (fderiv ℝ u x) x) :
    HasFDerivAt (fun y => ‖u y‖ ^ 2 / 2)
      ((2⁻¹ : ℝ) • (2 • (innerSL ℝ) (u x) ∘SL (fderiv ℝ u x))) x := by
  have h1 := hu.norm_sq
  have h2 := h1.mul_const (2⁻¹ : ℝ)
  simpa [div_eq_mul_inv] using h2

private theorem pressure_hasFDerivAt (p : EuclideanSpace ℝ (Fin 3) → ℝ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) (hp : HasFDerivAt p (fderiv ℝ p x) x) :
    HasFDerivAt (fun y => p y / ρ) ((ρ⁻¹ : ℝ) • (fderiv ℝ p x)) x := by
  have h := hp.mul_const (ρ⁻¹ : ℝ)
  simpa [div_eq_mul_inv] using h

/-- Kinetic-energy identity: the directional derivative of `‖u‖^2 / 2`
along `u x` equals `⟪u x, (fderiv ℝ u x) (u x)⟫`. -/
theorem kinetic_directional_deriv (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) (hu : HasFDerivAt u (fderiv ℝ u x) x) :
    (fderiv ℝ (fun y => ‖u y‖ ^ 2 / 2) x) (u x) =
      @inner ℝ _ _ (u x) ((fderiv ℝ u x) (u x)) := by
  have h := kinetic_hasFDerivAt u x hu
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]

/-- Bernoulli along a streamline: for steady incompressible inviscid flow
satisfying the Euler balance dotted with `u x`, with constant `ρ > 0` and
time-independent potential `Φ`, the directional derivative of the Bernoulli
head `p / ρ + ‖u‖^2 / 2 + Φ` along `u x` is zero. This is constancy along a
streamline, not global constancy. -/
theorem bernoulli_along_streamline (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hu : HasFDerivAt u (fderiv ℝ u x) x)
    (hp : HasFDerivAt p (fderiv ℝ p x) x)
    (hΦ : HasFDerivAt Φ (fderiv ℝ Φ x) x)
    (hEuler : @inner ℝ _ _ (u x) ((fderiv ℝ u x) (u x)) +
      (1 / ρ) * (fderiv ℝ p x) (u x) + (fderiv ℝ Φ x) (u x) = 0) :
    (fderiv ℝ (fun y => p y / ρ + ‖u y‖ ^ 2 / 2 + Φ y) x) (u x) = 0 := by
  have _hρ_pos : 0 < ρ := hρ
  have hP := pressure_hasFDerivAt p ρ x hp
  have hK := kinetic_hasFDerivAt u x hu
  have hH : HasFDerivAt (fun y => p y / ρ + ‖u y‖ ^ 2 / 2 + Φ y)
      ((ρ⁻¹ : ℝ) • (fderiv ℝ p x) + (2⁻¹ : ℝ) • (2 • (innerSL ℝ) (u x) ∘SL (fderiv ℝ u x)) +
        (fderiv ℝ Φ x)) x :=
    (hP.add hK).add hΦ
  rw [hH.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  linear_combination hEuler

end EarthScience
