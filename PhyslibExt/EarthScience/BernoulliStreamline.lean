/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.LinearCombination

/-!
# Bernoulli's theorem along a streamline

For steady incompressible inviscid flow satisfying the Euler balance with a
time-independent potential, the Bernoulli head `p / ρ + ‖u‖^2 / 2 + Φ` has zero
directional derivative along the velocity `u`, and is therefore constant along
each streamline. This is constancy along a streamline, not global constancy of
the Bernoulli head.

## i. Overview

The kinetic-energy identity says the directional derivative of `‖u‖^2 / 2`
along `u x` is the inner product of `u x` with the convective derivative
`(fderiv u x) (u x)`. Combining it with the pressure term and the potential
term, the directional derivative of the Bernoulli head along `u x` is the Euler
balance dotted with `u x`, which is zero by hypothesis. This is a local
differential condition at the single point `x`.

Constancy along a streamline needs the curve itself: along an integral curve
`γ` of `u` (a streamline of the steady flow), the chain rule turns that
directional derivative into the derivative of `t ↦ head (γ t)`, which therefore
vanishes on the whole parameter interval, and a function with zero derivative on
an open preconnected set is constant there.

Constant density `ρ > 0`, conservative body force, steady flow. No head loss, no
unsteady surface-wave claim, and no claim that the head is constant across
distinct streamlines.

## ii. Key results

- `EarthScience.kinetic_directional_deriv`: directional derivative of
  kinetic energy per unit mass.
- `EarthScience.bernoulli_head_directional_deriv_eq_zero`: the Bernoulli head
  has zero directional derivative along `u x` at a point `x` where the Euler
  balance holds.
- `EarthScience.bernoulli_along_streamline`: the Bernoulli head takes the same
  value at any two points of a streamline.

## iii. Table of contents

- A. Kinetic-energy identity
- B. Bernoulli along a streamline

## iv. References

- `HasFDerivAt` API in Mathlib, including `HasFDerivAt.norm_sq`;
  `IsIntegralCurveOn` and `IsOpen.is_const_of_deriv_eq_zero` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Kinetic-energy identity -/

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

/-! ## B. Bernoulli along a streamline -/

/-- Local form of Bernoulli's theorem: for steady incompressible inviscid flow
satisfying the Euler balance dotted with `u x`, with constant `ρ > 0` and
time-independent potential `Φ`, the directional derivative of the Bernoulli
head `p / ρ + ‖u‖^2 / 2 + Φ` along `u x` is zero at the point `x`. This is the
local differential condition behind `bernoulli_along_streamline`; by itself it
says nothing about the values of the head at other points. -/
theorem bernoulli_head_directional_deriv_eq_zero
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
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

/-- Bernoulli's theorem along a streamline: let `u` be a steady velocity field with
pressure `p`, potential `Φ` and constant density `ρ > 0`, and let `γ` be a streamline,
that is, an integral curve of `u` on an open preconnected set `s` of parameters (for
example an open interval). If `u`, `p` and `Φ` are differentiable at every point of
the streamline and the Euler balance dotted with `u` holds there, then the Bernoulli
head `p / ρ + ‖u‖^2 / 2 + Φ` takes the same value at any two points `γ a`, `γ b` of
the streamline. -/
theorem bernoulli_along_streamline
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : ℝ → EuclideanSpace ℝ (Fin 3)) {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : IsIntegralCurveOn γ (fun _ => u) s)
    (hu : ∀ t ∈ s, DifferentiableAt ℝ u (γ t))
    (hp : ∀ t ∈ s, DifferentiableAt ℝ p (γ t))
    (hΦ : ∀ t ∈ s, DifferentiableAt ℝ Φ (γ t))
    (hEuler : ∀ t ∈ s, @inner ℝ _ _ (u (γ t)) ((fderiv ℝ u (γ t)) (u (γ t))) +
      (1 / ρ) * (fderiv ℝ p (γ t)) (u (γ t)) + (fderiv ℝ Φ (γ t)) (u (γ t)) = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    p (γ a) / ρ + ‖u (γ a)‖ ^ 2 / 2 + Φ (γ a) =
      p (γ b) / ρ + ‖u (γ b)‖ ^ 2 / 2 + Φ (γ b) := by
  have hderiv : ∀ t ∈ s, HasDerivAt
      (fun τ => p (γ τ) / ρ + ‖u (γ τ)‖ ^ 2 / 2 + Φ (γ τ)) 0 t := by
    intro t ht
    have hγt : HasDerivAt γ (u (γ t)) t := (hγ t ht).hasDerivAt (hs.mem_nhds ht)
    have hH : HasFDerivAt (fun y => p y / ρ + ‖u y‖ ^ 2 / 2 + Φ y)
        ((ρ⁻¹ : ℝ) • (fderiv ℝ p (γ t)) +
          (2⁻¹ : ℝ) • (2 • (innerSL ℝ) (u (γ t)) ∘SL (fderiv ℝ u (γ t))) +
          (fderiv ℝ Φ (γ t))) (γ t) :=
      ((pressure_hasFDerivAt p ρ (γ t) (hp t ht).hasFDerivAt).add
        (kinetic_hasFDerivAt u (γ t) (hu t ht).hasFDerivAt)).add (hΦ t ht).hasFDerivAt
    have h0 := bernoulli_head_directional_deriv_eq_zero u p Φ ρ hρ (γ t)
      (hu t ht).hasFDerivAt (hp t ht).hasFDerivAt (hΦ t ht).hasFDerivAt (hEuler t ht)
    have hcomp := hH.differentiableAt.hasFDerivAt.comp_hasDerivAt t hγt
    rw [h0] at hcomp
    exact hcomp
  exact hs.is_const_of_deriv_eq_zero hs'
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hderiv t ht).deriv) ha hb

end EarthScience
