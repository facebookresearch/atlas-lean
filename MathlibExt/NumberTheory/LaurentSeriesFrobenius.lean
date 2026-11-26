/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotients

/-!
# Frobenius and continued fractions of Laurent series

Over a finite field with `q` elements, the `q`-th power map commutes with the partial quotient,
numerator and denominator recurrences for Laurent series at every index, including after a finite
continued fraction terminates (`laurentPartialQuotient_pow_card`).
-/

namespace MetaMathlibExt

variable {K : Type*} [Field K]

namespace laurentPartialQuotient_pow_card

open HahnSeries

-- Supports inside an additively closed set of exponents stay there under positive powers.
private theorem support_pow_succ_subset {S : Set ℤ} (hS : ∀ i ∈ S, ∀ j ∈ S, i + j ∈ S)
    {x : LaurentSeries K} (hx : x.support ⊆ S) (k : ℕ) : (x ^ (k + 1)).support ⊆ S := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ]
    refine support_mul_subset.trans ?_
    rintro _ ⟨i, hi, j, hj, rfl⟩
    exact hS i (ih hi) j (hx hj)

private theorem polyPart_add (x y : LaurentSeries K) :
    laurentPolyPart (x + y) = laurentPolyPart x + laurentPolyPart y := by
  ext n
  simp only [laurentPolyPart_coeff, coeff_add]
  split_ifs <;> simp

private theorem polyPart_eq_self {x : LaurentSeries K} (hx : x.support ⊆ Set.Iic 0) :
    laurentPolyPart x = x := by
  ext n
  rw [laurentPolyPart_coeff, ite_eq_left_iff]
  intro hn
  by_contra h
  exact hn (hx ((mem_support _ _).mpr (Ne.symm h)))

private theorem polyPart_eq_zero {x : LaurentSeries K} (hx : x.support ⊆ Set.Ioi 0) :
    laurentPolyPart x = 0 := by
  ext n
  rw [laurentPolyPart_coeff, coeff_zero, ite_eq_right_iff]
  intro hn
  by_contra h
  exact (not_lt.mpr hn) (hx ((mem_support _ _).mpr h))

variable [Fintype K]

private theorem pow_card_add (x y : LaurentSeries K) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (FiniteField.frobeniusAlgHom K (LaurentSeries K)) x y

private theorem pow_card_sub (x y : LaurentSeries K) :
    (x - y) ^ Fintype.card K = x ^ Fintype.card K - y ^ Fintype.card K :=
  map_sub (FiniteField.frobeniusAlgHom K (LaurentSeries K)) x y

private theorem polyPart_pow_card (α : LaurentSeries K) :
    laurentPolyPart (α ^ Fintype.card K) = laurentPolyPart α ^ Fintype.card K := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := K))
  -- `α` splits into its polynomial part, supported in exponents `≤ 0` (nonnegative powers of
  -- `x`), and a remainder supported in exponents `> 0`; the `q`-th power keeps both supports.
  have hpoly : (laurentPolyPart α ^ Fintype.card K).support ⊆ Set.Iic 0 := by
    rw [hk]
    refine support_pow_succ_subset (fun i hi j hj => Set.mem_Iic.mpr
      (add_nonpos (Set.mem_Iic.mp hi) (Set.mem_Iic.mp hj))) (fun n hn => ?_) k
    by_contra h
    exact (mem_support _ _).mp hn (by simp [laurentPolyPart_coeff, show ¬n ≤ 0 from h])
  have hrem : ((α - laurentPolyPart α) ^ Fintype.card K).support ⊆ Set.Ioi 0 := by
    rw [hk]
    refine support_pow_succ_subset (fun i hi j hj => Set.mem_Ioi.mpr
      (add_pos (Set.mem_Ioi.mp hi) (Set.mem_Ioi.mp hj))) (fun n hn => ?_) k
    by_contra h
    exact (mem_support _ _).mp hn
      (by simp [laurentPolyPart_coeff, not_lt.mp (show ¬0 < n from h)])
  calc laurentPolyPart (α ^ Fintype.card K)
      = laurentPolyPart (laurentPolyPart α ^ Fintype.card K +
          (α - laurentPolyPart α) ^ Fintype.card K) := by
        rw [← pow_card_add, add_sub_cancel]
    _ = laurentPolyPart α ^ Fintype.card K := by
        rw [polyPart_add, polyPart_eq_self hpoly, polyPart_eq_zero hrem, add_zero]

private theorem completeQuotient_pow_card (α : LaurentSeries K) (n : ℕ) :
    laurentCompleteQuotient (α ^ Fintype.card K) n =
      laurentCompleteQuotient α n ^ Fintype.card K := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [laurentCompleteQuotient]
    rw [ih, polyPart_pow_card, ← pow_card_sub, inv_pow]

private theorem partialQuotient_pow_card (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ Fintype.card K) n =
      laurentPartialQuotient α n ^ Fintype.card K := by
  simp only [laurentPartialQuotient]
  rw [completeQuotient_pow_card, polyPart_pow_card]

-- The convergents satisfy a two-step recursion, so we carry two consecutive indices.
private theorem conv_pow_card (α : LaurentSeries K) (n : ℕ) :
    (laurentConvNum (α ^ Fintype.card K) n = laurentConvNum α n ^ Fintype.card K ∧
        laurentConvDen (α ^ Fintype.card K) n = laurentConvDen α n ^ Fintype.card K) ∧
      laurentConvNum (α ^ Fintype.card K) (n + 1) =
          laurentConvNum α (n + 1) ^ Fintype.card K ∧
        laurentConvDen (α ^ Fintype.card K) (n + 1) =
          laurentConvDen α (n + 1) ^ Fintype.card K := by
  induction n with
  | zero =>
    simp [laurentConvNum, laurentConvDen, partialQuotient_pow_card, Fintype.card_ne_zero]
  | succ n ih =>
    refine ⟨ih.2, ?_, ?_⟩
    · simp only [laurentConvNum]
      rw [partialQuotient_pow_card, ih.1.1, ih.2.1, pow_card_add, mul_pow]
    · simp only [laurentConvDen]
      rw [partialQuotient_pow_card, ih.1.2, ih.2.2, pow_card_add, mul_pow]

end laurentPartialQuotient_pow_card

open laurentPartialQuotient_pow_card in
/-- **Frobenius acts on continued fractions of Laurent series.** Let $K$ be a finite field with
$q$ elements and let $\alpha \in K((x^{-1}))$. Write $b_n(\alpha)$, $P_n(\alpha)$ and
$Q_n(\alpha)$ for the terms of the partial quotient, numerator and denominator sequences.
The convention $0^{-1}=0$ extends these sequences past the end of a finite expansion.
For every $n \ge 0$, they satisfy $b_n(\alpha^q)=b_n(\alpha)^q$,
$P_n(\alpha^q)=P_n(\alpha)^q$ and $Q_n(\alpha^q)=Q_n(\alpha)^q$. The identities for $P$ and $Q$
also hold, trivially, for $n=-1$.

The numerator and denominator sequences store the initial values $P_{-1}=1$ and $Q_{-1}=0$ at
index $0$, and $P_n(\alpha)$ and $Q_n(\alpha)$ at index $n+1$. These latter terms give the
numerator and denominator of the ordinary $n$-th convergent whenever the expansion has one.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 2 (`integers-2026-A57-lem-2`). -/
public theorem laurentPartialQuotient_pow_card [Fintype K] (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ Fintype.card K) n =
        laurentPartialQuotient α n ^ Fintype.card K ∧
      laurentConvNum (α ^ Fintype.card K) n = laurentConvNum α n ^ Fintype.card K ∧
      laurentConvDen (α ^ Fintype.card K) n = laurentConvDen α n ^ Fintype.card K :=
  ⟨partialQuotient_pow_card α n, (conv_pow_card α n).1⟩

end MetaMathlibExt
