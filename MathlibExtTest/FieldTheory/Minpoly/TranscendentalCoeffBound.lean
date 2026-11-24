/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Minpoly.TranscendentalCoeffBound

@[expose] public section

open Polynomial

-- Consumer with the original binders.
example {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m :=
  Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    x hxL hx0 f hint m h₂ j c hc

-- The bound is vacuous without a coefficient representation: with `m = 0`
-- and `j` beyond the degree, the right-hand side is `0`, forcing `c = 0`
-- whenever the representation holds; here the degree inequality itself is
-- checked on a concrete zero coefficient.
example {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ 0)⁻¹ ∈ V)
    (j : ℕ)
    (hc : Polynomial.aeval x (0 : Polynomial L) =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    (0 : Polynomial L).natDegree ≤
      ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * 0 :=
  Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    x hxL hx0 f hint 0 h₂ j 0 hc
