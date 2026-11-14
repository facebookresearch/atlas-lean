/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.BernoulliStreamline

/-!
# Bernoulli along a streamline checks

Concrete consumers of `PhyslibExt.EarthScience.BernoulliStreamline`:
the kinetic identity for the identity flow, the public shape of the
Bernoulli theorem, and the degenerate zero-flow boundary case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For the
identity flow, the kinetic identity says the directional derivative of
`||x||^2 / 2` along `x` is `⟪x, x⟫`. For zero flow, zero pressure, and
zero potential, the Bernoulli head is identically zero.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Kinetic identity for the identity flow
- B. Bernoulli shape and zero-flow boundary
-/

/-- The public shape of the kinetic-energy identity. -/
example (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) (hu : HasFDerivAt u (fderiv ℝ u x) x) :
    (fderiv ℝ (fun y => ‖u y‖ ^ 2 / 2) x) (u x) =
      @inner ℝ _ _ (u x) ((fderiv ℝ u x) (u x)) :=
  EarthScience.kinetic_directional_deriv u x hu

/-- Kinetic identity for the identity flow: the directional derivative
of `‖x‖^2 / 2` along `x` is `⟪x, x⟫`. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2 / 2) x) x =
      @inner ℝ _ _ x x := by
  have hid : HasFDerivAt id (fderiv ℝ id x) x := by
    rw [fderiv_id]
    exact hasFDerivAt_id x
  have h := EarthScience.kinetic_directional_deriv id x hid
  rw [fderiv_id] at h
  simpa using h

/-- The public shape of the Bernoulli theorem. -/
example (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hu : HasFDerivAt u (fderiv ℝ u x) x)
    (hp : HasFDerivAt p (fderiv ℝ p x) x)
    (hΦ : HasFDerivAt Φ (fderiv ℝ Φ x) x)
    (hEuler : @inner ℝ _ _ (u x) ((fderiv ℝ u x) (u x)) +
      (1 / ρ) * (fderiv ℝ p x) (u x) + (fderiv ℝ Φ x) (u x) = 0) :
    (fderiv ℝ (fun y => p y / ρ + ‖u y‖ ^ 2 / 2 + Φ y) x) (u x) = 0 :=
  EarthScience.bernoulli_along_streamline u p Φ ρ hρ x hu hp hΦ hEuler

/-- Zero-flow boundary: zero velocity, pressure, and potential give
zero Bernoulli-head derivative. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun _y : EuclideanSpace ℝ (Fin 3) =>
      (0 : ℝ) / 1 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 / 2 + (0 : ℝ)) x)
      (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
  have hu : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (0 : EuclideanSpace ℝ (Fin 3)))
      (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) =>
        (0 : EuclideanSpace ℝ (Fin 3))) x) x := by
    simpa using hasFDerivAt_const (0 : EuclideanSpace ℝ (Fin 3)) x
  have hp : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ))
      (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) x) x := by
    simpa using hasFDerivAt_const (0 : ℝ) x
  have hΦ : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ))
      (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) x) x := by
    simpa using hasFDerivAt_const (0 : ℝ) x
  have hEuler : @inner ℝ _ _ (0 : EuclideanSpace ℝ (Fin 3))
        ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) =>
          (0 : EuclideanSpace ℝ (Fin 3))) x)
          (0 : EuclideanSpace ℝ (Fin 3))) +
      (1 / (1 : ℝ)) * (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) x)
        (0 : EuclideanSpace ℝ (Fin 3)) +
      (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) x)
        (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    simp
  have h := EarthScience.bernoulli_along_streamline
    (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : EuclideanSpace ℝ (Fin 3)))
    (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ))
    (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) 1 (by norm_num) x hu hp hΦ hEuler
  exact h
