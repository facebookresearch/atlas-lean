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
public import MathlibExt.Combinatorics.KnuthOldSumBinomialQuotients

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

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
