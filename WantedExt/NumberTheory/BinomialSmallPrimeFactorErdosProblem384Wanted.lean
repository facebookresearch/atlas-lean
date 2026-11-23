/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small prime factors of binomial coefficients (Erdős Problem 384)

Erdős Problem 384 (Erdős and Selfridge): if `1 < k < n - 1`, then `C(n, k)` is divisible by a prime
`p < n/2`, except `C(7, 3) = 5 · 7`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.BinomialSmallPrimeFactorErdosProblem384Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #384, https://www.erdosproblems.com/384 (status PROVED
(LEAN)). UnsolvedMath record UM-30006848 (`EP-384`), dataset ulamai/UnsolvedMath v1.8.0.

The bound is `p ≤ n/2` (written `2p ≤ n`), as in Ecklund's theorem and formal-conjectures: with the
strict bound printed on the page the statement fails, for example `C(4, 2) = 2 · 3` and `C(6, 2) = 3
· 5`. The exception `C(7, 3)` comes with its mirror `C(7, 4)`. `k < n - 1` is written `k + 1 < n`.
Compared with the formal-conjectures statement `ErdosProblems/384.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 384 (Erdős and Selfridge): if `1 < k < n - 1`, then `n.choose k` has a prime
factor `p ≤ n / 2`, except for `C(7, 3) = C(7, 4) = 5 · 7`. -/
def binomialHasPrimeFactorAtMostHalf : Prop :=
  ∀ n k : ℕ, 1 < k → k + 1 < n → (n, k) ≠ (7, 3) → (n, k) ≠ (7, 4) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/--
Resolved true: Ecklund proved that for `1 < k < n - 1` the binomial coefficient `C(n, k)` has a
prime factor `p ≤ n/2`, the only exceptions being `C(7, 3) = C(7, 4) = 35`; erdosproblems.com/384
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #384,
https://www.erdosproblems.com/384 (status PROVED (LEAN)); resolution: E. F. Ecklund, Jr., On prime
divisors of the binomial coefficient, Pacific J. Math. (1969), 267-270, Theorem: for n ≥ 2k, C(n, k)
has a prime divisor p ≤ n/2 when k ≥ 2, the only exception being C(7, 3); the range n/2 < k ≤ n - 2
follows from C(n, k) = C(n, n - k), https://msp.org/pjm/1969/29-2/p04.xhtml.
-/
public theorem_wanted binomialHasPrimeFactorAtMostHalf_holds : binomialHasPrimeFactorAtMostHalf

end MathlibExt.NumberTheory.BinomialSmallPrimeFactorErdosProblem384Wanted
