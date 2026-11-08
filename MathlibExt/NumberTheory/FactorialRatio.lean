/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Divisibility.Basic

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Integral factorial ratios

This file introduces the reusable predicate needed to state the classification
problem of K. Soundararajan's *Integral factorial ratios* (arXiv `1901.05133v1`,
`Factorials6.tex`, lines 83-91): for tuples of positive naturals `A = [a₁, …, aₖ]`
and `B = [b₁, …, bₗ]` with equal sums, the quotient
`(a₁n)! ⋯ (aₖn)! / ((b₁n)! ⋯ (bₗn)!)` is a natural number for every `n`.

The quotient is formalized through divisibility in `ℕ`: the denominator product
divides the numerator product. The `n = 0` case is automatic since every
factorial there equals one.

## Main declarations

* `factorialProd`: product of scaled factorials over a tuple at index `n`.
* `IsIntegralFactorialRatio`: the integral factorial-ratio predicate.
-/

@[expose] public section

/-- Product of the scaled factorials `(a * n)!` over the entries `a` of `L`. -/
def factorialProd (L : List ℕ) (n : ℕ) : ℕ :=
  (L.map fun a => Nat.factorial (a * n)).prod

/-- The integral factorial-ratio predicate from *Integral factorial ratios*:
both tuples consist of positive naturals, their sums agree (the paper's balance
condition `∑ aᵢ = ∑ bⱼ`), and the denominator product divides the numerator
product at every index `n`. -/
def IsIntegralFactorialRatio (A B : List ℕ) : Prop :=
  (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧ A.sum = B.sum ∧
    ∀ n : ℕ, factorialProd B n ∣ factorialProd A n

theorem factorialProd_nil (n : ℕ) : factorialProd [] n = 1 :=
  rfl

theorem factorialProd_cons (a : ℕ) (L : List ℕ) (n : ℕ) :
    factorialProd (a :: L) n =
      Nat.factorial (a * n) * factorialProd L n :=
  rfl

theorem factorialProd_perm {L₁ L₂ : List ℕ} (h : List.Perm L₁ L₂) (n : ℕ) :
    factorialProd L₁ n = factorialProd L₂ n := by
  unfold factorialProd
  exact (h.map _).prod_eq

/-- Every scaled factorial at index `0` equals `1`, so the whole product is `1`. -/
theorem factorialProd_zero (L : List ℕ) : factorialProd L 0 = 1 := by
  unfold factorialProd
  apply List.prod_eq_one
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rw [Nat.mul_zero, Nat.factorial_zero]

/-- The `n = 0` boundary always divides: both products are `1`. -/
theorem factorialProd_dvd_zero (A B : List ℕ) :
    factorialProd B 0 ∣ factorialProd A 0 := by
  rw [factorialProd_zero, factorialProd_zero]

/-- Transparent characterization of the predicate. -/
theorem isIntegralFactorialRatio_iff (A B : List ℕ) :
    IsIntegralFactorialRatio A B ↔
      (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧ A.sum = B.sum ∧
        ∀ n : ℕ, factorialProd B n ∣ factorialProd A n :=
  Iff.rfl

theorem IsIntegralFactorialRatio.pos_left {A B : List ℕ}
    (h : IsIntegralFactorialRatio A B) : ∀ a ∈ A, 0 < a :=
  h.1

theorem IsIntegralFactorialRatio.pos_right {A B : List ℕ}
    (h : IsIntegralFactorialRatio A B) : ∀ b ∈ B, 0 < b :=
  h.2.1

theorem IsIntegralFactorialRatio.sum_eq {A B : List ℕ}
    (h : IsIntegralFactorialRatio A B) : A.sum = B.sum :=
  h.2.2.1

theorem IsIntegralFactorialRatio.dvd {A B : List ℕ}
    (h : IsIntegralFactorialRatio A B) (n : ℕ) :
    factorialProd B n ∣ factorialProd A n :=
  h.2.2.2 n

theorem IsIntegralFactorialRatio.mk {A B : List ℕ}
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) (hsum : A.sum = B.sum)
    (hdvd : ∀ n : ℕ, factorialProd B n ∣ factorialProd A n) :
    IsIntegralFactorialRatio A B :=
  ⟨hA, hB, hsum, hdvd⟩

/-- The predicate is invariant under permuting the numerator tuple. -/
theorem isIntegralFactorialRatio_perm_left {A A' B : List ℕ}
    (hperm : List.Perm A A') (h : IsIntegralFactorialRatio A B) :
    IsIntegralFactorialRatio A' B := by
  obtain ⟨hA, hB, hsum, hdvd⟩ := h
  refine ⟨?_, hB, ?_, ?_⟩
  · intro a ha
    exact hA a ((hperm.symm.mem_iff).mp ha)
  · rw [← hperm.sum_eq]
    exact hsum
  · intro n
    rw [← factorialProd_perm hperm]
    exact hdvd n

/-- The predicate is invariant under permuting the denominator tuple. -/
theorem isIntegralFactorialRatio_perm_right {A B B' : List ℕ}
    (hperm : List.Perm B B') (h : IsIntegralFactorialRatio A B) :
    IsIntegralFactorialRatio A B' := by
  obtain ⟨hA, hB, hsum, hdvd⟩ := h
  refine ⟨hA, ?_, ?_, ?_⟩
  · intro b hb
    exact hB b ((hperm.symm.mem_iff).mp hb)
  · rw [← hperm.sum_eq]
    exact hsum
  · intro n
    rw [← factorialProd_perm hperm]
    exact hdvd n

/-- The predicate is invariant under permuting both tuples. -/
theorem isIntegralFactorialRatio_perm {A A' B B' : List ℕ}
    (hA : List.Perm A A') (hB : List.Perm B B') (h : IsIntegralFactorialRatio A B) :
    IsIntegralFactorialRatio A' B' :=
  isIntegralFactorialRatio_perm_right hB (isIntegralFactorialRatio_perm_left hA h)

/-- Equal tuples always satisfy the predicate. -/
theorem isIntegralFactorialRatio_refl (L : List ℕ) (hpos : ∀ a ∈ L, 0 < a) :
    IsIntegralFactorialRatio L L :=
  ⟨hpos, hpos, rfl, fun _ => dvd_rfl⟩

/-- Equal singleton tuples satisfy the predicate. -/
theorem isIntegralFactorialRatio_singleton_self (c : ℕ) (hc : 0 < c) :
    IsIntegralFactorialRatio [c] [c] := by
  refine ⟨?_, ?_, rfl, fun _ => dvd_rfl⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    exact hc
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact hc

/-- Central-binomial example: `[(2)] / [(1), (1)]` is integral, since
`(n! * n!) ∣ (2 * n)!`. -/
theorem isIntegralFactorialRatio_centralBinom :
    IsIntegralFactorialRatio [2] [1, 1] := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    decide
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
    rw [hb]
    decide
  · intro n
    have h := Nat.factorial_mul_factorial_dvd_factorial_add n n
    have h2 : n + n = 2 * n := by omega
    rw [h2] at h
    simpa [factorialProd] using h
