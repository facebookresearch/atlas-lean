/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

@[expose] public section

open MonomialOrder MathlibExt.RingTheory.MvPolynomial.GroebnerBasis

namespace MathlibExtTest.RingTheory.MvPolynomial.GroebnerBasis

/-- Non-vacuity: a single nonzero polynomial is a Gröbner basis of the principal ideal it
generates, for any monomial order. -/
theorem singleton_isGroebnerBasis (m : MonomialOrder (Fin 2)) (b : MvPolynomial (Fin 2) ℚ)
    (hb : b ≠ 0) : IsGroebnerBasis m {b} (Ideal.span {b}) := by
  refine ⟨Ideal.subset_span, fun f hf hf0 ↦ ⟨b, rfl, hb, ?_⟩⟩
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  have hq : q ≠ 0 := by rintro rfl; simp at hf0
  rw [m.degree_mul hq hb]
  exact le_add_self

/-- Membership test by the remainder criterion: `x₁ ∉ (x₀)`, because `x₁ = 0 · x₀ + x₁` is a
division of `x₁` by `{x₀}` whose remainder `x₁` is nonzero. -/
example : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∉ Ideal.span {MvPolynomial.X 0} := by
  have hG := singleton_isGroebnerBasis degLex (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)
    (MvPolynomial.X_ne_zero 0)
  rw [hG.mem_iff_remainder_eq_zero degLex _ 0 (MvPolynomial.X 1) (by simp)]
  · exact MvPolynomial.X_ne_zero 1
  · intro c hc b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hc
    subst hc
    rw [degree_X]
    intro h
    simpa using h 0

/-- The empty set is a Gröbner basis of the zero ideal. -/
example (m : MonomialOrder (Fin 2)) :
    IsGroebnerBasis m (∅ : Set (MvPolynomial (Fin 2) ℚ)) ⊥ :=
  ⟨by simp, fun f hf hf0 ↦ absurd ((Submodule.mem_bot _).1 hf) hf0⟩

end MathlibExtTest.RingTheory.MvPolynomial.GroebnerBasis
