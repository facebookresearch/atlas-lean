/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.BuchbergerCriterion
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

@[expose] public section

open MonomialOrder MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
  MathlibExt.RingTheory.MvPolynomial.BuchbergerCriterion

namespace MathlibExtTest.RingTheory.MvPolynomial.BuchbergerCriterion

/-- Non-vacuity: a single nonzero polynomial passes Buchberger's test (its only S-polynomial is
`S(b, b) = 0`), so it is a Gröbner basis of the principal ideal it generates. -/
example (m : MonomialOrder (Fin 2)) (b : MvPolynomial (Fin 2) ℚ) (hb : b ≠ 0) :
    IsGroebnerBasis m {b} (Ideal.span {b}) := by
  refine isGroebnerBasis_of_sPolynomial m {b} (by simpa [eq_comm] using hb) ?_
  rintro g rfl h rfl
  exact ⟨0, by simp, fun _ ↦ by simp⟩

/-- The two variables `x₀, x₁` form a Gröbner basis of `(x₀, x₁)` for degree-lexicographic
order, by Buchberger's criterion applied to the S-polynomial `S(x₀, x₁) = x₁ x₀ - x₀ x₁ = 0`. -/
example : IsGroebnerBasis degLex ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) ℚ)) (Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}) := by
  refine isGroebnerBasis_of_sPolynomial degLex _ ?_ ?_
  · simp [eq_comm, MvPolynomial.X_ne_zero]
  · intro g hg h hh
    have e10 : (Finsupp.single 1 1 - Finsupp.single 0 1 : Fin 2 →₀ ℕ) = Finsupp.single 1 1 := by
      ext i; fin_cases i <;> simp
    have e01 : (Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 2 →₀ ℕ) = Finsupp.single 0 1 := by
      ext i; fin_cases i <;> simp
    have hS : degLex.sPolynomial g h = 0 := by
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
        simp only [MonomialOrder.sPolynomial, degLex.degree_X, degLex.leadingCoeff_X, e10, e01,
          sub_self] <;>
        simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, add_comm]
    exact ⟨0, by simp [hS], fun _ ↦ by simp⟩

end MathlibExtTest.RingTheory.MvPolynomial.BuchbergerCriterion
