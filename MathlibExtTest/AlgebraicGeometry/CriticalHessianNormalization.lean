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
different from two: for the stabilization `g = f + z²`, the normal direction
`∂_z` is Hessian-orthogonal to the smaller chart, and the form on it is one half
of the Hessian of `z²`. This catches forgetting the source's half-Hessian.
-/

/-- The pointwise normalization on a Hessian-orthogonal vector: with Hessian
`diag(h, 2)` (smaller chart along the first axis, one normal direction), a vector `(a, b)`
orthogonal to the first axis (`a * h = 0`) has half-Hessian `b²`, the square of its normal
component, whatever `h` is. -/
example {k : Type} [Field k] (h a b : k) (horth : a * h = 0) (two_ne_zero : (2 : k) ≠ 0) :
    (2 : k)⁻¹ * (a * a * h + b * b * 2) = b * b := by
  rw [show a * a * h = a * (a * h) by ring, horth, mul_zero, zero_add]
  field_simp

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
