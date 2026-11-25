/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Prime.Nth

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Mandl's inequality for the sum of the first $n$ primes.** Let $p_k$ denote the $k$-th
prime, so that $p_1 = 2$. For every natural number $n \ge 9$, twice the sum of the first $n$
primes is at most $n$ times the $n$-th prime: $2(p_1 + \cdots + p_n) \le n \, p_n$.

Dusart proved the inequality for every $n \ge 9$, as quoted by Axler.

Source: Christian Axler, "On a Sequence Involving Prime Numbers,"
Journal of Integer Sequences 18 (2015), source equation (101), lines 89-107,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Axler/axler6.tex.
Complete-source SHA-256
d14106761bbab2548473a1d8321e1a79953158fe2e3c36551926473c3851c14b;
raw lines 89-107 joined with LF and no terminal LF SHA-256
cf4e5fb018d3b12e931f0527d0262598e3186bcd26654762946952009b961479. -/
theorem_wanted mandl_prime_sum_inequality (n : ℕ) (hn : 9 ≤ n) :
    2 * (∑ k ∈ Finset.range n, Nat.nth Nat.Prime k) ≤
      n * Nat.nth Nat.Prime (n - 1)

end

end MetaMathlibExt
