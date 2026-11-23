/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors

/-! # Products of divisors and super-m-Zumkeller numbers -/

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

/-- **Product of the divisors.** For a natural number $n$, $T(n)$ is the product of all positive
divisors of $n$. For $n = 0$ the set of divisors is taken to be empty, so $T(0) = 1$. -/
def divisorProd (n : ℕ) : ℕ := ∏ d ∈ n.divisors, d

/-- **Super-m-Zumkeller numbers.** For a natural number $n$, let $T(n)$ be the product of the
positive divisors of $n$ (for $n = 0$ the divisor set is taken to be empty, so $T(0) = 1$).
Then $n$ is *super-m-Zumkeller* if there is a set $A$ of positive divisors of $T(n)$ such that
the product of the elements of $A$ equals the product of the positive divisors of $T(n)$ that
are not in $A$; that is, the divisors of $T(n)$ split into two complementary sets, one of which
may be empty, with equal products. -/
def IsSuperMZumkeller (n : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ (divisorProd n).divisors ∧
    (∏ d ∈ A, d) = ∏ d ∈ (divisorProd n).divisors \ A, d

/-- **$k$-m-perfect numbers.** For natural numbers $k$ and $n$, $n$ is $k$-m-perfect if
$T(n) = n^k$, where $T(n)$ is the product of the divisors of $n$. -/
def IsKMPerfect (k n : ℕ) : Prop := divisorProd n = n ^ k

/-- **Square of the product of the divisors.** For every positive integer $n$, let $T(n)$ be the
product of the positive divisors of $n$ and $\tau(n)$ their number. Then $T(n)^2 = n^{\tau(n)}$.

The paper writes this as $T(n) = n^{\tau(n)/2}$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Lemma 1. -/
theorem divisorProd_sq (n : ℕ) (hn : 0 < n) :
    (divisorProd n) ^ 2 = n ^ (n.divisors.card) := by
  calc
    (divisorProd n) ^ 2 = ∏ d ∈ n.divisors, d * (n / d) := by
      rw [Finset.prod_mul_distrib, sq]
      exact congrArg (divisorProd n * ·) (Nat.prod_div_divisors n id).symm
    _ = ∏ _d ∈ n.divisors, n := by
      apply Finset.prod_congr rfl
      intro d hd
      exact Nat.mul_div_cancel' (by simpa [Nat.mem_divisors, hn.ne'] using hd)
    _ = _ := Finset.prod_const _

/-- **Super-m-Zumkeller numbers $n \ge 2$ have at least three divisors.** If a natural number
$n \ge 2$ is super-m-Zumkeller, then the number $\tau(n)$ of positive divisors of $n$ satisfies
$\tau(n) \ge 3$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 1. -/
theorem three_le_card_divisors_of_isSuperMZumkeller (n : ℕ)
    (hn : 2 ≤ n) (h : IsSuperMZumkeller n) :
    3 ≤ n.divisors.card := by
  have hnp : ¬ n.Prime := by
    intro hp
    have hT : divisorProd n = n := by simp [divisorProd, hp.divisors, hp.ne_one.symm]
    obtain ⟨A, hA, hprod⟩ := h
    rw [hT] at hA hprod
    apply hp.prime.not_isSquare
    refine ⟨∏ d ∈ A, d, ?_⟩
    calc
      n = ∏ d ∈ n.divisors, d := hT.symm
      _ = _ := by rw [← Finset.prod_sdiff hA, ← hprod]
  obtain ⟨d, hd, hd1, hdn⟩ := Nat.exists_dvd_of_not_prime hn hnp
  have hn0 : n ≠ 0 := by omega
  exact Finset.two_lt_card_iff.mpr ⟨d, 1, n, Nat.mem_divisors.mpr ⟨hd, hn0⟩,
    Nat.one_mem_divisors.mpr hn0, Nat.mem_divisors_self n hn0, hd1, hdn, by omega⟩

end MathlibExt.NumberTheory.SuperMZumkellerWanted
