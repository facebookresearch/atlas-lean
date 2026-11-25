/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.TruncatedQuotient

@[expose] public section

open MvPolynomial

-- `exactSource` consumer with the original binders and inline relations.
example (p : ℕ) (hp : 0 < p) (n a b : ℕ) (hab : a < b) :
    Finite (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ∧
      Nat.card (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ≤ p ^ (n * b) :=
  MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
    p hp n a b hab

-- The public relation set unfolds to the three inline relations.
example (p n a b : ℕ) :
    Ideal.span (truncatedDieudonneRelations p n a b) =
      Ideal.span ({X true * X false - C (p : ℤ), X false ^ n,
        X true ^ b - X true ^ a} : Set (MvPolynomial Bool ℤ)) := by
  rw [truncatedDieudonneRelations_eq]

-- Boundary: when `n = 0`, the bound is `p ^ 0 = 1`; indeed the second
-- relation is `1`, so the quotient is a subsingleton.
example (p : ℕ) (hp : 0 < p) (a b : ℕ) (hab : a < b) :
    Nat.card (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ 0, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ≤ 1 := by
  have h := (MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
    p hp 0 a b hab).2
  simpa using h
