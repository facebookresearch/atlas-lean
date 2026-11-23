/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CriticalCanonicalLineModels
import Mathlib.Tactic.NormNum

/-!
The actual universal-coordinate Hessian of z squared is two. Its normal
quadratic form is therefore one, including in positive characteristic
different from two: for the stabilization `g = f + z²` with the projection as
normal-form retraction, `g - f ∘ α = z²`. This catches forgetting the source's
half-Hessian. For an identity embedding, `g - f ∘ α = g - g` has zero Hessian,
matching the zero normal quotient, whatever the Hessian of `g` is.
-/

open Polynomial
open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions

noncomputable section

variable {k : Type} [Field k] (E : DifferentialCoordinates k k[X] 1)

private theorem coordinate_derivative_X (coordinate : E.coordinate 0 = (X : k[X])) :
    coordinateDerivation E 0 (X : k[X]) = 1 := by
  change E.basis.coord 0 (KaehlerDifferential.D k k[X] X) = 1
  have h : E.basis 0 = KaehlerDifferential.D k k[X] X := by
    rw [E.basis_eq, coordinate]
  rw [← h]
  simp

private theorem quadratic_hessian (coordinate : E.coordinate 0 = (X : k[X])) :
    hessian E ((X : k[X]) ^ 2) 0 0 = 2 := by
  have h : coordinateDerivation E 0 ((X : k[X]) ^ 2) = X + X := by
    rw [pow_two, Derivation.leibniz]
    simp [coordinate_derivative_X E coordinate]
  change coordinateDerivation E 0 (coordinateDerivation E 0 (X ^ 2)) = 2
  rw [h, map_add, coordinate_derivative_X E coordinate]
  norm_num [coordinate_derivative_X E coordinate]

example (coordinate : E.coordinate 0 = (X : k[X])) (two_ne_zero : (2 : k) ≠ 0) :
    (2 : k)⁻¹ * Polynomial.eval 0 (hessian E ((X : k[X]) ^ 2) 0 0) = 1 := by
  rw [quadratic_hessian E coordinate]
  simp only [eval_ofNat]
  exact inv_mul_cancel₀ two_ne_zero

/-- Identity embedding: the normal-form function `g - g` has zero Hessian. -/
example (g : k[X]) : hessian E (g - g) 0 0 = 0 := by
  simp [hessian]
