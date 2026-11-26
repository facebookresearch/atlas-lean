/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/844.lean` (Formal Conjectures), for the definitions and statement.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.PrimeCounting
import MathlibExt.Combinatorics.SetFamily.ChvatalShifted

/-!
# Erdős Problem 844

`conjecture_holds` proves Erdős Problem 844: for every $N$, a largest set
$A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all $a, b \in A$ consists of
the even numbers and the odd non-squarefree numbers in $\{1, \dots, N\}$. The proof follows
Weisenberg's argument, which deduces the bound from a theorem of Chvátal on intersecting
subfamilies of shifted down-sets.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem844Wanted

/-! Source record `FC-ErdosProblem844`, ported from FormalConjectures
`ErdosProblems/844.lean` and checked against erdosproblems.com/844.
The upstream `answer(True)` is dropped. Status: resolved true externally;
`conjecture_holds` below proves it, following Weisenberg's proof through Chvátal's theorem on
shifted down-sets. -/

/-- **Even or odd non-squarefree numbers up to a bound.** For a natural number $N$, the set of
integers $n$ with $1 \le n \le N$ that are even or not squarefree, that is, the even numbers in
$\{1, \dots, N\}$ together with the odd non-squarefree numbers in $\{1, \dots, N\}$. -/
def evenOrOddNonSquarefree (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 2 ∣ n ∨ ¬ Squarefree n)

/-- **Erdős Problem 844.** For a natural number $N$, let $E_N$ be the set of integers $n$ with
$1 \le n \le N$ that are even or not squarefree. The statement that for every natural number $N$,
the largest size of a set $A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all
$a, b \in A$ (including $a = b$) is the size of $E_N$. -/
def conjecture : Prop :=
  ∀ N : ℕ,
    IsGreatest {k : ℕ | ∃ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = k}
      (evenOrOddNonSquarefree N).card

open Finset

/-! ### Squarefree numbers as sets of prime indices -/

section PrimeIndices

/-- The product of the primes $p_i$ over the indices $i \in A$, where $p_0 = 2$. -/
private noncomputable def primeProd (A : Finset ℕ) : ℕ := ∏ i ∈ A, Nat.nth Nat.Prime i

/-- The indices of the prime factors of $n$. -/
private def primeIdx (n : ℕ) : Finset ℕ := n.primeFactors.image (Nat.count Nat.Prime)

private lemma nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) :=
  Nat.nth_injective (p := Nat.Prime) Nat.infinite_setOfPred_prime

private lemma nth_prime_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono (p := Nat.Prime) Nat.infinite_setOfPred_prime

private lemma primeProd_eq_prod_image (A : Finset ℕ) :
    primeProd A = ∏ p ∈ A.image (Nat.nth Nat.Prime), p := by
  rw [primeProd, prod_image fun i _ j _ h => nth_prime_injective h]

private lemma primeFactors_primeProd (A : Finset ℕ) :
    (primeProd A).primeFactors = A.image (Nat.nth Nat.Prime) := by
  rw [primeProd_eq_prod_image]
  refine Nat.primeFactors_prod fun p hp => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.1 hp
  exact Nat.prime_nth_prime i

private lemma squarefree_primeProd (A : Finset ℕ) : Squarefree (primeProd A) := by
  have h := Nat.squarefree_prod_primeFactors (primeProd A)
  rwa [primeFactors_primeProd, ← primeProd_eq_prod_image] at h

private lemma primeProd_pos (A : Finset ℕ) : 0 < primeProd A :=
  prod_pos fun i _ => (Nat.prime_nth_prime i).pos

private lemma primeIdx_primeProd (A : Finset ℕ) : primeIdx (primeProd A) = A := by
  rw [primeIdx, primeFactors_primeProd, image_image]
  conv_rhs => rw [← image_id (s := A)]
  exact image_congr fun i _ =>
    Nat.count_nth_of_infinite (p := Nat.Prime) Nat.infinite_setOfPred_prime i

private lemma primeProd_primeIdx {n : ℕ} (hn : Squarefree n) : primeProd (primeIdx n) = n := by
  have hinj : Set.InjOn (Nat.count Nat.Prime) n.primeFactors := fun p hp q hq h =>
    Nat.count_injective (p := Nat.Prime) (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) h
  rw [primeProd, primeIdx, prod_image hinj]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  exact prod_congr rfl fun p hp => Nat.nth_count (Nat.prime_of_mem_primeFactors hp)

private lemma primeProd_le_of_subset {A B : Finset ℕ} (h : B ⊆ A) : primeProd B ≤ primeProd A :=
  prod_le_prod_of_subset_of_one_le h fun i _ _ => (Nat.prime_nth_prime i).one_lt.le

private lemma primeProd_shift_le {A : Finset ℕ} {i j : ℕ} (hj : j ∈ A) (hij : i < j)
    (hiA : i ∉ A) : primeProd (insert i (A.erase j)) ≤ primeProd A := by
  have hi : i ∉ A.erase j := fun h => hiA (mem_of_mem_erase h)
  unfold primeProd
  rw [prod_insert hi, ← mul_prod_erase A _ hj]
  exact Nat.mul_le_mul_right _ (nth_prime_strictMono hij).le

private lemma add_two_le_primeProd {A : Finset ℕ} {i : ℕ} (hi : i ∈ A) : i + 2 ≤ primeProd A :=
  (Nat.add_two_le_nth_prime i).trans
    (Nat.le_of_dvd (primeProd_pos A) (dvd_prod_of_mem (Nat.nth Nat.Prime) hi))

private lemma zero_mem_iff_two_dvd (A : Finset ℕ) : 0 ∈ A ↔ 2 ∣ primeProd A := by
  constructor
  · intro h
    rw [← Nat.nth_prime_zero_eq_two]
    exact dvd_prod_of_mem (Nat.nth Nat.Prime) h
  · intro h
    have h2 : 2 ∈ (primeProd A).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.prime_two, h, (primeProd_pos A).ne'⟩
    rw [primeFactors_primeProd] at h2
    obtain ⟨i, hi, hi2⟩ := mem_image.1 h2
    rw [← Nat.nth_prime_zero_eq_two] at hi2
    rwa [nth_prime_injective hi2] at hi

/-- The sets of prime indices whose products are at most $N$, that is, the squarefree numbers in
$\{1, \dots, N\}$. -/
private noncomputable def primeFamily (N : ℕ) : Finset (Finset ℕ) :=
  (range N).powerset.filter fun A => primeProd A ≤ N

private lemma mem_primeFamily {N : ℕ} {A : Finset ℕ} : A ∈ primeFamily N ↔ primeProd A ≤ N := by
  rw [primeFamily, mem_filter, mem_powerset]
  refine ⟨And.right, fun h => ⟨fun i hi => mem_range.2 ?_, h⟩⟩
  have := add_two_le_primeProd hi
  omega

private lemma isLowerSet_primeFamily (N : ℕ) :
    IsLowerSet ((primeFamily N : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro A B hBA hA
  rw [mem_coe, mem_primeFamily] at hA ⊢
  exact (primeProd_le_of_subset hBA).trans hA

private lemma shift_primeFamily (N : ℕ) :
    ∀ A ∈ primeFamily N, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ primeFamily N := by
  intro A hA j hj i hij hiA
  rw [mem_primeFamily] at hA ⊢
  exact (primeProd_shift_le hj hij hiA).trans hA

/-- A set of squarefree numbers in $\{1, \dots, N\}$ with no squarefree pairwise product has at
most as many elements as the even squarefree numbers in $\{1, \dots, N\}$. -/
private lemma card_le_card_even_squarefree {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Icc 1 N)
    (hsq : ∀ a ∈ T, Squarefree a) (hpair : ∀ a ∈ T, ∀ b ∈ T, ¬ Squarefree (a * b)) :
    #T ≤ #((evenOrOddNonSquarefree N).filter Squarefree) := by
  have hinj : Set.InjOn primeIdx T := fun a ha b hb h => by
    rw [← primeProd_primeIdx (hsq a ha), ← primeProd_primeIdx (hsq b hb), h]
  have hsub : T.image primeIdx ⊆ primeFamily N := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    rw [mem_primeFamily, primeProd_primeIdx (hsq a ha)]
    exact (mem_Icc.1 (hT ha)).2
  have hint : ((T.image primeIdx : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting := by
    intro A hA B hB hAB
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hB
    apply hpair a ha b hb
    have h := squarefree_primeProd (primeIdx a ∪ primeIdx b)
    rwa [primeProd, prod_union hAB, ← primeProd, ← primeProd, primeProd_primeIdx (hsq a ha),
      primeProd_primeIdx (hsq b hb)] at h
  calc #T = #(T.image primeIdx) := (Finset.card_image_of_injOn hinj).symm
    _ ≤ #{A ∈ primeFamily N | 0 ∈ A} :=
      Combinatorics.ChvatalShifted.card_le_card_star_zero_of_isLowerSet_of_shifted
        (isLowerSet_primeFamily N) (shift_primeFamily N) hsub hint
    _ ≤ #((evenOrOddNonSquarefree N).filter Squarefree) := by
      refine card_le_card_of_injOn primeProd (fun A hA => ?_) fun A _ B _ h => ?_
      · obtain ⟨hA, h0⟩ := mem_filter.1 (mem_coe.1 hA)
        rw [mem_primeFamily] at hA
        rw [mem_coe, mem_filter, evenOrOddNonSquarefree, mem_filter, mem_Icc]
        exact ⟨⟨⟨primeProd_pos A, hA⟩, Or.inl ((zero_mem_iff_two_dvd A).1 h0)⟩,
          squarefree_primeProd A⟩
      · rw [← primeIdx_primeProd A, ← primeIdx_primeProd B, h]

end PrimeIndices

/--
**Erdős Problem 844 is true.** For every natural number $N$, the largest size of a set
$A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all $a, b \in A$ (including
$a = b$) is the number of integers $n$ with $1 \le n \le N$ that are even or not squarefree.

Source: B. Alexeev, D.
Mixon, and W. Sawin, The independence and clique cover numbers of the squarefree graph,
arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928; Erdős Problems, Problem 844
(including Desmond Weisenberg's proof), https://www.erdosproblems.com/latex/844. Moved from
`OpenConjectures/NumberTheory/ErdosProblem844`.
-/
public theorem conjecture_holds : conjecture := by
  intro N
  refine ⟨⟨evenOrOddNonSquarefree N, filter_subset _ _, fun a ha b hb hab => ?_, rfl⟩, ?_⟩
  · rw [evenOrOddNonSquarefree, mem_filter] at ha hb
    rcases ha.2 with ha2 | ha2
    · rcases hb.2 with hb2 | hb2
      · obtain ⟨x, rfl⟩ := ha2
        obtain ⟨y, rfl⟩ := hb2
        have h := hab 2 ⟨x * y, by ring⟩
        exact absurd (Nat.isUnit_iff.1 h) (by norm_num)
      · exact hb2 hab.of_mul_right
    · exact ha2 hab.of_mul_left
  · rintro k ⟨A, hA, hpair, rfl⟩
    calc #A = #(A.filter Squarefree) + #(A.filter fun n => ¬ Squarefree n) :=
          (card_filter_add_card_filter_not _).symm
      _ ≤ #((evenOrOddNonSquarefree N).filter Squarefree) +
          #((evenOrOddNonSquarefree N).filter fun n => ¬ Squarefree n) := by
        refine add_le_add (card_le_card_even_squarefree ((filter_subset _ _).trans hA)
          (fun a ha => (mem_filter.1 ha).2)
          fun a ha b hb => hpair a (mem_filter.1 ha).1 b (mem_filter.1 hb).1) ?_
        refine card_le_card fun n hn => ?_
        obtain ⟨hn, hsq⟩ := mem_filter.1 hn
        rw [mem_filter, evenOrOddNonSquarefree, mem_filter]
        exact ⟨⟨hA hn, Or.inr hsq⟩, hsq⟩
      _ = #(evenOrOddNonSquarefree N) := card_filter_add_card_filter_not _

end MathlibExt.NumberTheory.ErdosProblem844Wanted
