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

end MathlibExt.NumberTheory.SuperMZumkellerWanted
