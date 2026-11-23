/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.ResultantMagnitude

@[expose] public section

set_option autoImplicit false

/-- Exact-source consumer, using the original binders verbatim. -/
example (P Q : Polynomial ℚ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P ≠ 0 →
        |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant Q| ≤
          |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P|) :
    P = Q :=
  Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le P Q hP hQ hdeg S hS₁ hS₂ h

/-- Exact-source consumer for the integer variant, using the original binders. -/
example (P Q : Polynomial ℤ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P ≠ 0 →
        ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant Q).natAbs ≤
          ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P).natAbs) :
    P = Q :=
  Polynomial.eq_of_forall_natAbs_resultant_X_pow_add_C_le P Q hP hQ hdeg S hS₁ hS₂ h

/-- Boundary example: with `S` bounded above, the comparison does not apply. -/
example : ¬ ∀ b : ℤ, ∃ c ∈ (∅ : Set ℤ), b ≤ c := by
  intro h
  obtain ⟨c, hc, -⟩ := h 0
  exact hc
