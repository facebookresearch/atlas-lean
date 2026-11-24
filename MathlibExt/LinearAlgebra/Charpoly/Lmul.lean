/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Minimal and characteristic polynomials of left multiplication

If the natural degree of `minpoly K x` is the finrank of the
finite-dimensional algebra `E`, the characteristic polynomial of left
multiplication by `x` is the minimal polynomial. Both are monic, the
minimal polynomial divides the characteristic polynomial by the existing
Cayley--Hamilton evaluation theorem, and their natural degrees agree.

The underlying polynomial-evaluation, integrality and minimal-polynomial
transport facts are supplied by Mathlib's algebra-homomorphism APIs.
The algebra need not be commutative, reduced or a domain. Finite
dimensionality already supplies the integrality of `x`.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace LinearMap

section Primitive

variable {K E : Type*} [Field K] [Ring E] [Algebra K E]
  [FiniteDimensional K E]

/-- If the minimal polynomial of `x` has natural degree equal to the
finrank of the algebra, it is the characteristic polynomial of left
multiplication by `x`. Finite dimensionality supplies integrality. -/
theorem charpoly_lmul_eq_minpoly_of_natDegree_eq_finrank
    (x : E) (hDeg : (minpoly K x).natDegree = Module.finrank K E) :
    (Algebra.lmul K E x).charpoly = minpoly K x := by
  have hdvd : minpoly K x ∣ (Algebra.lmul K E x).charpoly :=
    minpoly.dvd K x (Algebra.aeval_self_charpoly_lmul x)
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite K x)) (charpoly_monic _) hdvd
  rw [charpoly_natDegree, hDeg]

end Primitive

end LinearMap
