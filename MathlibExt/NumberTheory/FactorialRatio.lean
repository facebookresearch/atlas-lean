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

/-- **Product of scaled factorials.** For a list $L$ of natural numbers and a natural number
$n$, the product of scaled factorials of $L$ at $n$ is $\prod_{a \in L} (an)!$, the product of the
factorials $(an)!$ over the entries $a$ of $L$, counted with multiplicity; for the empty list it
is $1$. -/
def factorialProd (L : List ℕ) (n : ℕ) : ℕ :=
  (L.map fun a => Nat.factorial (a * n)).prod

/-- **Integral factorial ratio.** For lists $A = (a_1, \dots, a_k)$ and
$B = (b_1, \dots, b_l)$ of natural numbers, the pair $(A, B)$ is an integral
factorial ratio when every $a_i$ and every $b_j$ is positive,
$a_1 + \dots + a_k = b_1 + \dots + b_l$, and for every natural number $n$ the product
$(b_1 n)! \cdots (b_l n)!$ divides $(a_1 n)! \cdots (a_k n)!$; equivalently, the quotient
$\frac{(a_1 n)! \cdots (a_k n)!}{(b_1 n)! \cdots (b_l n)!}$ is a natural number.

Source: K. Soundararajan, *Integral factorial ratios* (arXiv 1901.05133). -/
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

/-- **Scaled factorial product at index zero.** For every list $L$ of natural numbers,
$\prod_{a \in L} (a \cdot 0)! = 1$, since every factor equals $0! = 1$. -/
theorem factorialProd_zero (L : List ℕ) : factorialProd L 0 = 1 := by
  unfold factorialProd
  apply List.prod_eq_one
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rw [Nat.mul_zero, Nat.factorial_zero]

/-- **Scaled factorial products at index zero divide.** For all lists $A$ and $B$ of natural
numbers, $\prod_{b \in B} (b \cdot 0)!$ divides $\prod_{a \in A} (a \cdot 0)!$, since both
products equal $1$. -/
theorem factorialProd_dvd_zero (A B : List ℕ) :
    factorialProd B 0 ∣ factorialProd A 0 := by
  rw [factorialProd_zero, factorialProd_zero]

/-- **Characterization of integral factorial ratios.** For lists $A$ and $B$ of natural numbers,
$(A, B)$ is an integral factorial ratio if and only if every entry of $A$ is positive, every
entry of $B$ is positive, the entries of $A$ and the entries of $B$ have the same sum, and for
every natural number $n$ the product $\prod_{b \in B} (bn)!$ divides $\prod_{a \in A} (an)!$. -/
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

/-- **Permuting the numerator of an integral factorial ratio.** Let $A$, $A'$ and $B$ be lists of
natural numbers such that $A'$ is a permutation of $A$. If $(A, B)$ is an integral factorial
ratio, then so is $(A', B)$. -/
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

/-- **Permuting the denominator of an integral factorial ratio.** Let $A$, $B$ and $B'$ be lists
of natural numbers such that $B'$ is a permutation of $B$. If $(A, B)$ is an integral factorial
ratio, then so is $(A, B')$. -/
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

/-- **Integral factorial ratios are invariant under permutation.** Let $A$, $A'$, $B$ and $B'$ be
lists of natural numbers such that $A'$ is a permutation of $A$ and $B'$ is a permutation of
$B$. If $(A, B)$ is an integral factorial ratio, then so is $(A', B')$. -/
theorem isIntegralFactorialRatio_perm {A A' B B' : List ℕ}
    (hA : List.Perm A A') (hB : List.Perm B B') (h : IsIntegralFactorialRatio A B) :
    IsIntegralFactorialRatio A' B' :=
  isIntegralFactorialRatio_perm_right hB (isIntegralFactorialRatio_perm_left hA h)

/-- **Equal tuples form an integral factorial ratio.** If every entry of a list $L$ of natural
numbers is positive, then $(L, L)$ is an integral factorial ratio. -/
theorem isIntegralFactorialRatio_refl (L : List ℕ) (hpos : ∀ a ∈ L, 0 < a) :
    IsIntegralFactorialRatio L L :=
  ⟨hpos, hpos, rfl, fun _ => dvd_rfl⟩

/-- **Equal singletons form an integral factorial ratio.** For every positive natural number
$c$, the one-entry tuples $(c)$ and $(c)$ form an integral factorial ratio. -/
theorem isIntegralFactorialRatio_singleton_self (c : ℕ) (hc : 0 < c) :
    IsIntegralFactorialRatio [c] [c] := by
  refine ⟨?_, ?_, rfl, fun _ => dvd_rfl⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    exact hc
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact hc

/-- **The central binomial factorial ratio is integral.** The tuples $(2)$ and $(1, 1)$ form an
integral factorial ratio: their entries are positive, their sums agree ($2 = 1 + 1$), and for
every natural number $n$, $n! \cdot n!$ divides $(2n)!$. -/
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
