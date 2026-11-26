/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The power-sum criterion over a finite field

The moments of degrees up to `q - 1` detect whether a list of `q` elements enumerates the
field: the polynomial `1 - (X - c) ^ (q - 1)` is the indicator of each value `c`.

## References

* Chandan Kumar Vishwakarma and Rajesh P. Singh, [*A Congruence Identity on Ordered
  Partitions Using Permutation Polynomials*](https://math.colgate.edu/~integers/y12/y12.pdf),
  INTEGERS 24 (2024), Article A12, pp. 1–11, Lemma 3.
* Rudolf Lidl and Harald Niederreiter, *Finite Fields*, 2nd ed., Encyclopedia of Mathematics
  and its Applications 20, Cambridge University Press (1997), Lemma 7.3 (cited by Lemma 3).
-/

namespace MetaMathlibExt

open Finset

private theorem one_sub_pow_card_sub_one {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (x : K) :
    1 - x ^ (Fintype.card K - 1) = if x = 0 then 1 else 0 := by
  split_ifs with hx
  · simp [hx, zero_pow (Nat.sub_ne_zero_of_lt Fintype.one_lt_card)]
  · rw [FiniteField.pow_card_sub_one_eq_one x hx, sub_self]

/-- **Power-sum criterion for distinct elements of a finite field.** Let $K$ be a finite field
with $q$ elements and let $a_1, \dots, a_q \in K$. Then $a_1, \dots, a_q$ are pairwise distinct
if and only if $\sum_{i=1}^{q} a_i^t = 0$ for every $t = 0, 1, \dots, q - 2$ and
$\sum_{i=1}^{q} a_i^{q-1} = -1$, where $0^0 = 1$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 3
(`integers-2024-A12-lem-3`). -/
public theorem injective_iff_sum_pow_eq {K : Type*} [Field K] [Fintype K]
    (a : Fin (Fintype.card K) → K) :
    Function.Injective a ↔
      (∀ t : ℕ, t < Fintype.card K - 1 → ∑ i, a i ^ t = 0) ∧
        ∑ i, a i ^ (Fintype.card K - 1) = -1 := by
  classical
  let n := Fintype.card K - 1
  change Function.Injective a ↔ (∀ t : ℕ, t < n → ∑ i, a i ^ t = 0) ∧ ∑ i, a i ^ n = -1
  have hcard : (Fintype.card K : K) = 0 := FiniteField.cast_card_eq_zero K
  have hsurj : Function.Injective a ↔ Function.Surjective a :=
    Finite.injective_iff_surjective_of_equiv (Fintype.equivFin K).symm
  constructor
  · intro ha
    have hsum (t : ℕ) : (∑ i, a i ^ t) = ∑ x : K, x ^ t :=
      (Equiv.ofBijective a ⟨ha, hsurj.mp ha⟩).sum_comp (fun x : K => x ^ t)
    refine ⟨fun t ht => (hsum t).trans (FiniteField.sum_pow_lt_card_sub_one K t ht), ?_⟩
    rw [hsum]
    have h : (∑ x : K, (1 - x ^ n)) = 1 := by
      simp [n, one_sub_pow_card_sub_one]
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_one, hcard, zero_sub] at h
    exact neg_eq_iff_eq_neg.mp h
  · rintro ⟨hlower, htop⟩
    apply hsurj.mpr
    intro c
    -- In the binomial expansion only the moment of degree n survives.
    have hshift : (∑ i, (a i - c) ^ n) = -1 := calc
      _ = ∑ t ∈ range (n + 1), (∑ i, a i ^ t) * ((-c) ^ (n - t) * (n.choose t : K)) := by
        simp_rw [sub_eq_add_neg, add_pow, mul_assoc]
        rw [sum_comm]
        simp_rw [sum_mul]
      _ = -1 := by
        refine (sum_eq_single n ?_ (by simp)).trans ?_
        · intro t ht hne
          rw [hlower t (lt_of_le_of_ne (Nat.le_of_lt_succ (mem_range.mp ht)) hne), zero_mul]
        · simp [htop]
    have hfibre : (∑ i, (1 - (a i - c) ^ n)) = 1 := by
      rw [sum_sub_distrib, hshift, sum_const, card_univ, Fintype.card_fin, nsmul_one, hcard]
      simp
    -- The field-valued count need only be nonzero to rule out an empty fibre.
    by_contra! hc
    simp [n, one_sub_pow_card_sub_one, sub_eq_zero, hc] at hfibre

end MetaMathlibExt
