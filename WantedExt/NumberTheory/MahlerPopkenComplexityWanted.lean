/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.MahlerPopkenComplexity.BinaryUpperBound
public import MathlibExt.NumberTheory.MahlerPopkenComplexityMahlerPopkenComplexityTwoEqRecursionValue

/-!
# Recursions for Mahler–Popken complexity

Statements from John M. Campbell, "A Binary Version of the
Mahler-Popken Complexity Function", *INTEGERS* 24 (2024),
Article A94 (<https://math.colgate.edu/~integers/y94/y94.pdf>).

Proposition 1 is split into its general-`m` part, where the paper
only asserts the recursion (9) "for all sufficiently large `n`",
and its explicit binary part, where (9) holds for `n ≥ 3`; the
binary part is proved in
`MathlibExt.NumberTheory.MahlerPopkenComplexityMahlerPopkenComplexityTwoEqRecursionValue`.  The
side conditions `d ≠ 1`, `d ≠ n`, and `0 < η` are the ones the paper
imposes when discussing the classical recursion (8).
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

/-- **The $m$-ary complexity eventually satisfies its recursion.** For every natural number
$m \ge 1$ there is $N$ such that for every $n \ge N$, the $m$-ary Mahler–Popken complexity
$\|n\|_m$ equals the right-hand side of the recursion (9), that is, the least of the values
$\|d\|_m + \|n/d\|_m$ over divisors $d$ of $n$ with $d \ne 1$ and $d \ne n$, and the values
$\|\eta\|_m + \|n - \eta\|_m$ over $0 < \eta < n$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem_wanted mahlerPopkenComplexity_eq_recursionValue_eventually
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      mahlerPopkenComplexity m n = mahlerPopkenRecursionValue m n

end MahlerPopkenComplexityWanted

end NumberTheory

end MathlibExt
