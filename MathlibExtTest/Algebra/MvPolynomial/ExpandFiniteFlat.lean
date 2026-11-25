/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.ExpandFiniteFlat

@[expose] public section

open MvPolynomial

-- `exactSource` consumer with the original binders.
example (R : Type) [CommRing R] (σ : Type) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Finite ∧
      (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Flat ∧
      ∀ q : PrimeSpectrum (MvPolynomial σ R),
        (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q =
          p ^ Nat.card σ :=
  MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow R σ p hp

-- Higher-universe consumer: the statement is universe-polymorphic.
example (R : Type 1) [CommRing R] (σ : Type 1) [Finite σ] (p : ℕ) (hp : 0 < p)
    (q : PrimeSpectrum (MvPolynomial σ R)) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q =
      p ^ Nat.card σ :=
  (MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow R σ p hp).2.2 q

-- Boundary: with one variable and `p = 2`, every fibre has rank `2`.
example (q : PrimeSpectrum (MvPolynomial (Fin 1) ℤ)) :
    (MvPolynomial.expand 2 (σ := Fin 1) (R := ℤ)).toRingHom.finrank q = 2 := by
  have h := (MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow
    ℤ (Fin 1) 2 (by norm_num)).2.2 q
  simpa using h
