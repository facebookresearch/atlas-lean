/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.Elimination

@[expose] public section

open MonomialOrder MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
  MathlibExt.RingTheory.MvPolynomial.Elimination

namespace MathlibExtTest.RingTheory.MvPolynomial.Elimination

/-- In two variables `x₀ > x₁`, the set `{1}` of the variable `x₁` is a final segment. -/
theorem final_segment : ∀ i ∉ ({1} : Set (Fin 2)), ∀ j ∈ ({1} : Set (Fin 2)), i < j := by
  intro i hi j hj
  rw [Set.mem_singleton_iff] at hi hj
  subst hj
  fin_cases i
  · decide
  · exact absurd rfl hi

/-- Non-vacuity: a lexicographic Gröbner basis of `I ⊆ ℚ[x₀, x₁]` yields one of `I ∩ ℚ[x₁]`. -/
example {G : Set (MvPolynomial (Fin 2) ℚ)} {I : Ideal (MvPolynomial (Fin 2) ℚ)}
    (hG : IsGroebnerBasis lex G I) (f : MvPolynomial (Fin 2) ℚ) (hf : f ∈ I)
    (hfS : f ∈ MvPolynomial.supported ℚ {1}) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ∈ MvPolynomial.supported ℚ {1} ∧ g ≠ 0 ∧ lex.degree g ≤ lex.degree f :=
  elimination hG final_segment f hf hfS hf0

/-- The variable `x₁` lies in `ℚ[x₁]`. -/
example : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∈ MvPolynomial.supported ℚ {1} :=
  MvPolynomial.X_mem_supported.2 rfl

/-- The lexicographic lemma: `x₁² ≤ x₁³` and `x₁³` vanishes at `x₀`, so `x₁²` does. -/
example : (Finsupp.single (1 : Fin 2) 2 : Fin 2 →₀ ℕ) 0 = 0 :=
  lex_le_vanish final_segment (d := Finsupp.single 1 2) (e := Finsupp.single 1 3)
    (Finsupp.toLex_monotone (Finsupp.single_mono (by norm_num))) (by
      intro i hi; rw [Set.mem_singleton_iff] at hi; simp [Ne.symm hi])
    0 (by simp)

end MathlibExtTest.RingTheory.MvPolynomial.Elimination
