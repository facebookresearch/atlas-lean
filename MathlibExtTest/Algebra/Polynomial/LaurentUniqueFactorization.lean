/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LaurentUniqueFactorization

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.EuclideanDomain

@[expose] public section

open LaurentPolynomial

universe u v

/-- Consumer with the original binders and universe. -/
private theorem exactSource (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  LaurentPolynomial.uniqueFactorizationMonoid R

/-- The result also gives the instance in a higher universe. -/
example (R : Type (max u v)) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  LaurentPolynomial.uniqueFactorizationMonoid R

/-- Concrete case: Laurent polynomials over the integers. -/
example : UniqueFactorizationMonoid (LaurentPolynomial ℤ) :=
  LaurentPolynomial.uniqueFactorizationMonoid ℤ
