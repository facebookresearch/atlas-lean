/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.HomogeneousPDeriv

/-! # Consumers for iterated derivatives of homogeneous polynomials -/

namespace MvPolynomialHomogeneousPDerivTest

open MvPolynomial

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {σ R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ)
    {i : ℕ} (hi : n < i) : (MvPolynomial.pderiv k)^[i] φ = 0 :=
  hφ.iterate_pderiv_eq_zero_of_lt k hi

/-- At the boundary `i = n` the result need not vanish: differentiating
`X 0` once gives `1`. This checks that `n < i` is load-bearing. -/
public example : (pderiv (0 : Fin 1))^[1] (X (0 : Fin 1) :
    MvPolynomial (Fin 1) ℚ) = 1 := by
  simp

end MvPolynomialHomogeneousPDerivTest
