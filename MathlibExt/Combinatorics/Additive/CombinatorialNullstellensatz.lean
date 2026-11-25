/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Alon's Combinatorial Nullstellensatz in the source's form, and Chevalley–Warning

Mathlib proves both theorems of N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput.
8 (1999) 7–29: `MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination`
(Theorem 1.1) and `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`
(Theorem 1.2). This file restates them with finitely many variables in the notation of the
paper, with the degree bound `deg hᵢ ≤ deg f - deg gᵢ` of Theorem 1.1 and the exponent vector
`(t₁, …, t_n)` of Theorem 1.2, and derives the form of the Chevalley–Warning theorem proved in
Section 3 of the paper from Mathlib's divisibility version `char_dvd_card_solutions_of_sum_lt`.

Mathlib also has the paper's Theorem 3.2 (Cauchy–Davenport, `ZMod.cauchy_davenport`) and the
Erdős–Ginzburg–Ziv theorem of its Proposition 8.2 (`ZMod.erdos_ginzburg_ziv`, for every `n`, not
only primes); they are not restated.
-/

@[expose] public section

open MvPolynomial Finset

namespace MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz

variable {F σ : Type*} [Field F] [Fintype σ]

/-- **Combinatorial Nullstellensatz, Theorem 1.1.** Let `F` be a field, `f` a polynomial in the
variables `xᵢ` (`i ∈ σ`, finitely many), `Sᵢ` nonempty finite subsets of `F`, and
`gᵢ = ∏_{s ∈ Sᵢ} (xᵢ - s)`. If `f` vanishes at every point of `∏ᵢ Sᵢ`, then
`f = ∑ᵢ hᵢ gᵢ` for polynomials `hᵢ` with `deg hᵢ ≤ deg f - deg gᵢ` (N. Alon, "Combinatorial
Nullstellensatz", Combin. Probab. Comput. 8 (1999), Theorem 1.1). The degree bound is stated
as `deg hᵢ + deg gᵢ ≤ deg f`, which is the same for `hᵢ ≠ 0` and avoids truncated subtraction;
the paper's "moreover" clause about subrings is not included. This restates Mathlib's
`MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination` in the paper's notation. -/
theorem exists_eq_sum_mul_of_vanishing (S : σ → Finset F) (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ F) (hf : ∀ x : σ → F, (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ h : σ → MvPolynomial σ F,
      (∀ i, h i = 0 ∨ (h i).totalDegree + (∏ s ∈ S i, (X i - C s)).totalDegree ≤
        f.totalDegree) ∧
      f = ∑ i, h i * ∏ s ∈ S i, (X i - C s) := by
  obtain ⟨h, hdeg, hfeq⟩ := combinatorial_nullstellensatz_exists_linearCombination S hS f hf
  refine ⟨fun i => h i, fun i => ?_, ?_⟩
  · by_cases hi : h i = 0
    · exact Or.inl hi
    · right
      have hg : (∏ s ∈ S i, (X i - C s) : MvPolynomial σ F) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun s _ hzero => by
          classical
          have := congrArg (fun q : MvPolynomial σ F => q.coeff (Finsupp.single i 1)) hzero
          have h0 : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
          simp [coeff_X, coeff_C, h0] at this
      have := hdeg i
      rw [totalDegree_mul_of_isDomain hg hi] at this
      dsimp only
      omega
  · rw [hfeq, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]

/-- **Combinatorial Nullstellensatz, Theorem 1.2.** Let `F` be a field and `f` a polynomial in
finitely many variables `xᵢ` (`i ∈ σ`) of total degree `∑ᵢ tᵢ`, where the coefficient of the
monomial `∏ᵢ xᵢ^{tᵢ}` in `f` is nonzero. If `Sᵢ ⊆ F` are finite sets with `|Sᵢ| > tᵢ`, then
there is a point `s ∈ ∏ᵢ Sᵢ` with `f(s) ≠ 0` (N. Alon, "Combinatorial Nullstellensatz", Combin.
Probab. Comput. 8 (1999), Theorem 1.2). This restates Mathlib's
`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero` with an exponent function
instead of a finsupp. -/
theorem exists_eval_ne_zero (f : MvPolynomial σ F) (t : σ → ℕ)
    (hdeg : f.totalDegree = ∑ i, t i) (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0)
    (S : σ → Finset F) (hS : ∀ i, t i < (S i).card) :
    ∃ s : σ → F, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 := by
  refine combinatorial_nullstellensatz_exists_eval_nonzero f (Finsupp.equivFunOnFinite.symm t)
    hcoeff ?_ S fun i => by simpa using hS i
  rw [hdeg, Finsupp.degree_eq_sum]
  simp

/-- **Chevalley–Warning theorem, existence form.** Let `K` be a finite field and `f_j`
(`j ∈ s`) polynomials in finitely many variables `xᵢ` (`i ∈ σ`) whose total degrees sum to less
than the number of variables. If the `f_j` have a common zero `x`, then they have another common
zero `y ≠ x` (N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999),
Theorem 3.1, stated there over the prime fields `ℤ_p` and proved with Theorem 1.2; here it is
deduced for every finite field from Mathlib's `char_dvd_card_solutions_of_sum_lt`, which says the
number of common zeros is divisible by the characteristic). -/
theorem exists_ne_common_zero {K ι : Type*} [Field K] [Finite K] {s : Finset ι}
    {f : ι → MvPolynomial σ K}
    (hdeg : ∑ j ∈ s, (f j).totalDegree < Fintype.card σ) {x : σ → K}
    (hx : ∀ j ∈ s, eval x (f j) = 0) :
    ∃ y : σ → K, y ≠ x ∧ ∀ j ∈ s, eval y (f j) = 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hprime : p.Prime := CharP.char_is_prime K p
  have hdvd := char_dvd_card_solutions_of_sum_lt p hdeg
  have hpos : 0 < Fintype.card { x : σ → K // ∀ j ∈ s, eval x (f j) = 0 } :=
    Fintype.card_pos_iff.2 ⟨⟨x, hx⟩⟩
  have htwo : 2 ≤ Fintype.card { x : σ → K // ∀ j ∈ s, eval x (f j) = 0 } :=
    hprime.two_le.trans (Nat.le_of_dvd hpos hdvd)
  obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card htwo ⟨x, hx⟩
  exact ⟨y, fun h => hne (Subtype.ext h), hy⟩

end MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz
