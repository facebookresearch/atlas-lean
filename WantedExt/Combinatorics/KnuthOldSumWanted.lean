/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Combinatorial identities inspired by Knuth's old sum

Statements from Akalu Tefera and Aklilu Zeleke, "Combinatorial
Identities Inspired by Knuth's Old Sum", *INTEGERS* 26 (2026),
Article A68 (<https://math.colgate.edu/~integers/aa68/aa68.pdf>),
DOI `10.5281/zenodo.20597521`.

For nonnegative integers `n` and `j`, with `N = n + 2j + 1`, the
paper studies the alternating sum
`S(n, j) = Σ_{k=0}^n C(N, n-k)·(2^{n-k} + 1)·2^{n-k-1}·(-1)^k`.
The factor `(2^m + 1)·2^{m-1}` is written here in the equal form
`(4^m + 2^m)/2` over `ℚ`, which is also valid at `m = 0` (the
`k = n` term); by Lemma 1 of the paper it is the number of words
of length `m` over a four-letter alphabet with an even number of
`a`'s.  Theorem 2's right side is printed as
`C(2j+k, k)·2^{k-1}·(1 + 2^k·3^{n-k})`, written here in the equal
form `C(2j+k, k)·(2^k + 4^k·3^{n-k})/2`, valid at `k = 0`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

/-- **Weight in Knuth's old sum.** For a natural number $m$, the weight $w(m)$ is the rational
number $(4^m + 2^m)/2$, which equals $(2^m + 1) 2^{m-1}$.

It is the number of words of length $m$ over a four-letter alphabet in which a fixed letter
occurs an even number of times. -/
def knuthOldSumWeight (m : ℕ) : ℚ := ((4 : ℚ) ^ m + (2 : ℚ) ^ m) / 2

/-- **Counting words with an even number of $a$'s.** For every natural number $n$, the number of
words of length $n$ over the four-letter alphabet $\{a, b, c, d\}$ in which the letter $a$ occurs
an even number of times is $(4^n + 2^n)/2$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Lemma 1. -/
theorem_wanted card_evenACount_words (n : ℕ) :
    Nat.card {w : Fin n → Fin 4 //
      Even (Finset.univ.filter (fun i => w i = 0)).card} =
        (4 ^ n + 2 ^ n) / 2

/-- **Tefera–Zeleke identity with binomial quotients.** Let $n$ and $j$ be natural numbers, let
$N = n + 2j + 1$, and let $w(m) = (4^m + 2^m)/2$ be the weight in Knuth's old sum. Then, in the
rational numbers,
$$\sum_{k=0}^{n} \binom{N}{n-k} w(n-k) (-1)^k
= \binom{N}{n} \sum_{k=0}^{n} \frac{\binom{n}{k}}{\binom{2j+1+k}{2j+1}} w(n-k) (-1)^k.$$

This is Equation (1) of the paper, whose weight $(2^m + 1) 2^{m-1}$ is written here as
$(4^m + 2^m)/2$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Theorem 1. -/
theorem_wanted knuthOldSum_eq_mul_sum_div (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 2 * j + 1) (n - k) : ℚ) *
        knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k) =
      (Nat.choose (n + 2 * j + 1) n : ℚ) *
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℚ) /
            (Nat.choose (2 * j + 1 + k) (2 * j + 1) : ℚ)) *
            knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k

/-- **Tefera–Zeleke identity with powers of $2$, $3$ and $4$.** Let $n$ and $j$ be natural numbers,
let $N = n + 2j + 1$, and let $w(m) = (4^m + 2^m)/2$ be the weight in Knuth's old sum. Then, in the
rational numbers,
$$\sum_{k=0}^{n} \binom{N}{n-k} w(n-k) (-1)^k
= \sum_{k=0}^{n} \binom{2j+k}{k} \frac{2^k + 4^k 3^{n-k}}{2}.$$

This is Equation (2) of the paper, which prints the weight as $(2^m + 1) 2^{m-1}$ and the terms
on the right as $\binom{2j+k}{k} 2^{k-1} (1 + 2^k 3^{n-k})$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Theorem 2. -/
theorem_wanted knuthOldSum_eq_sum_pow (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 2 * j + 1) (n - k) : ℚ) *
        knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * j + k) k : ℚ) *
          (((2 : ℚ) ^ k + (4 : ℚ) ^ k * (3 : ℚ) ^ (n - k)) / 2)

end MathlibExt.Combinatorics.KnuthOldSumWanted
