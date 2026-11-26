/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# The Elimination Theorem

For the lexicographic order `x₀ > x₁ > ⋯`, a Gröbner basis of an ideal `I` contains a Gröbner
basis of every elimination ideal: if `S` is a final segment of the variables (every variable
outside `S` comes before every variable in `S`), then the elements of a Gröbner basis `G` of `I`
that involve only the variables in `S` form a Gröbner basis of `I ∩ k[S]`. This is how Gröbner
bases eliminate variables, project varieties and solve polynomial systems triangularly.

The key fact is a property of the lexicographic order: a monomial below a monomial in the
variables of `S` is itself a monomial in the variables of `S`.

The subring `k[S]` is Mathlib's `MvPolynomial.supported K S`.

Sources: B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 9, Definition 9.12,
Example 9.13 (lexicographic order is an elimination order) and Theorem 9.14 (Elimination Theorem);
see also D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 3, §1 (section
only).
-/

@[expose] public section

noncomputable section

namespace MathlibExt.RingTheory.MvPolynomial.Elimination

open _root_.MvPolynomial MonomialOrder MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
open scoped MonomialOrder

variable {σ K : Type*} [LinearOrder σ] [WellFoundedGT σ] [Field K]

omit [LinearOrder σ] [WellFoundedGT σ] in
/-- Membership in `k[S]` monomial by monomial. -/
private theorem mem_supported_iff {S : Set σ} {f : _root_.MvPolynomial σ K} :
    f ∈ supported K S ↔ ∀ d ∈ f.support, ∀ i ∉ S, d i = 0 := by
  classical
  rw [mem_supported]
  constructor
  · intro h d hd i hi
    by_contra hdi
    exact hi (h ((mem_vars_iff_mem_support i).2 ⟨d, hd, Finsupp.mem_support_iff.2 hdi⟩))
  · intro h i hi
    obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
    by_contra hiS
    exact Finsupp.mem_support_iff.1 hid (h d hd i hiS)

omit [WellFoundedGT σ] in
/-- **Lexicographic order and final segments of variables.** If every variable outside `S` comes
before every variable in `S`, and the exponent vector `e` vanishes outside `S`, then every `d`
that is lexicographically at most `e` vanishes outside `S`. -/
theorem lex_le_vanish {S : Set σ} (hS : ∀ i ∉ S, ∀ j ∈ S, i < j) {d e : σ →₀ ℕ}
    (hde : toLex d ≤ toLex e) (he : ∀ i ∉ S, e i = 0) : ∀ i ∉ S, d i = 0 := by
  intro i0 hi0
  by_contra hd0
  have hne : d ≠ e := fun h ↦ hd0 (h ▸ he i0 hi0)
  have hlt : toLex d < toLex e := lt_of_le_of_ne hde (fun h ↦ hne (toLex.injective h))
  obtain ⟨i, hpre, hi⟩ := Finsupp.Lex.lt_iff.1 hlt
  by_cases hiS : i ∈ S
  · have : i0 < i := hS i0 hi0 i hiS
    exact hd0 ((hpre i0 this).trans (he i0 hi0))
  · have h0 : (ofLex (toLex e)) i = 0 := he i hiS
    simp only [ofLex_toLex] at hi h0
    omega

/-- **Elimination Theorem** (B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture
9, Theorem 9.14, with Example 9.13; see also Cox–Little–O'Shea, *Ideals, Varieties, and
Algorithms*, Ch. 3 §1, section only). Let `G` be a Gröbner basis of `I` for the lexicographic order
and `S` a final segment of the variables. Then the leading monomial of every nonzero `f ∈ I ∩ k[S]`
is divisible by the leading monomial of an element of `G ∩ k[S]`: `G ∩ k[S]` is a Gröbner basis of
`I ∩ k[S]` in the leading-monomial sense of `IsGroebnerBasis`. Here `k[S]` is
`MvPolynomial.supported K S`. -/
theorem elimination {G : Set (_root_.MvPolynomial σ K)} {I : Ideal (_root_.MvPolynomial σ K)}
    (hG : IsGroebnerBasis lex G I) {S : Set σ} (hS : ∀ i ∉ S, ∀ j ∈ S, i < j) :
    ∀ f ∈ I, f ∈ supported K S → f ≠ 0 →
      ∃ g ∈ G, g ∈ supported K S ∧ g ≠ 0 ∧ lex.degree g ≤ lex.degree f := by
  intro f hf hfS hf0
  obtain ⟨g, hgG, hg0, hgf⟩ := hG.2 f hf hf0
  refine ⟨g, hgG, ?_, hg0, hgf⟩
  have hdf : ∀ i ∉ S, lex.degree f i = 0 :=
    mem_supported_iff.1 hfS _ ((lex.degree_mem_support_iff f).2 hf0)
  have hdg : ∀ i ∉ S, lex.degree g i = 0 := fun i hi ↦
    Nat.eq_zero_of_le_zero ((hgf i).trans (hdf i hi).le)
  refine mem_supported_iff.2 fun d hd ↦ ?_
  exact lex_le_vanish hS (lex_le_iff.1 (lex.le_degree hd)) hdg

end MathlibExt.RingTheory.MvPolynomial.Elimination
