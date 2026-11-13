/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Prescribed largest prime factors of `n` and `n + 1` (Erdős Problem 649)

Erdős Problem 649: let `P(m)` denote the greatest prime factor of `m`. Is it true that, for any two
primes `p, q`, there exists some integer `n` such that `P(n) = p` and `P(n + 1) = q`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.ConsecutiveLargestPrimeFactorsErdosProblem649Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #649, https://www.erdosproblems.com/649 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006969 (`EP-649`), dataset ulamai/UnsolvedMath v1.8.0.

The two primes are taken distinct (for `p = q` no `n` works, `p` dividing both `n` and `n + 1`). The
problem page notes that the question as written fails for `p = 2, q = 7` and discusses amendments
('odd primes', 'all sufficiently large primes'); the second target is the weakest of these, the
claim for all sufficiently large distinct primes, whose refutation answers every amended form.
`P(m)` is the largest element of `m.primeFactors`. Compared with the formal-conjectures statement
`ErdosProblems/649.lean` (the first target matches `erdos_649`; no code imported).
-/

/-- The largest prime factor `P(m)` of `m` (`0` for `m ≤ 1`). -/
def largestPrimeFactor (m : ℕ) : ℕ :=
  m.primeFactors.sup id

/-- Erdős Problem 649, as posed: for any two distinct primes `p, q` there is an integer `n` with
`P(n) = p` and `P(n + 1) = q`. -/
def consecutiveLargestPrimeFactors : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ∃ n : ℕ, largestPrimeFactor n = p ∧ largestPrimeFactor (n + 1) = q

/-- Erdős Problem 649 with the weakest amendment discussed on the problem page: for all
sufficiently large distinct primes `p, q` there is an integer `n` with `P(n) = p` and
`P(n + 1) = q`. -/
def consecutiveLargestPrimeFactorsLargePrimes : Prop :=
  ∃ N : ℕ, ∀ p q : ℕ, p.Prime → q.Prime → N ≤ p → N ≤ q → p ≠ q →
    ∃ n : ℕ, largestPrimeFactor n = p ∧ largestPrimeFactor (n + 1) = q

/--
Resolved false: no `n` has `P(n) = 2` and `P(n + 1) = 7`, since `n` would be a power of `2` and `2^k
≢ -1 (mod 7)`; erdosproblems.com/649 lists the problem as disproved, with a Lean proof of the
formal-conjectures statement. Source: T. F. Bloom, Erdős Problems, Problem #649,
https://www.erdosproblems.com/649 (status DISPROVED (LEAN)); resolution: erdosproblems.com/649: the
obstruction 2^k ≢ -1 (mod 7), and A. Tong's quadratic-reciprocity argument recorded on the page, for
every prime p there are infinitely many primes q (any prime q ≡ -1 mod 4m, m the product of the
primes ≤ p) such that no n has P(n) = p and P(n + 1) = q, https://www.erdosproblems.com/649.
-/
public theorem_wanted consecutiveLargestPrimeFactors_refuted : ¬ consecutiveLargestPrimeFactors

/--
Resolved false: by Tong's argument on erdosproblems.com/649, for a prime `p` let `m` be the product
of the primes up to `p` and `q ≡ -1 (mod 4m)` a prime (infinitely many exist); if `P(n) = p` then
every prime factor of `n` is a quadratic residue modulo `q` by quadratic reciprocity, hence so is
`n`, while `-1` is not (`q ≡ 3 mod 4`), so `q ∤ n + 1`. Choosing `p` and then `q` beyond any bound
refutes the claim for large primes. Source: T. F. Bloom, Erdős Problems, Problem #649,
https://www.erdosproblems.com/649 (status DISPROVED (LEAN)); resolution: erdosproblems.com/649: the
obstruction 2^k ≢ -1 (mod 7), and A. Tong's quadratic-reciprocity argument recorded on the page, for
every prime p there are infinitely many primes q (any prime q ≡ -1 mod 4m, m the product of the
primes ≤ p) such that no n has P(n) = p and P(n + 1) = q, https://www.erdosproblems.com/649.
-/
public theorem_wanted consecutiveLargestPrimeFactorsLargePrimes_refuted :
    ¬ consecutiveLargestPrimeFactorsLargePrimes

end MathlibExt.NumberTheory.ConsecutiveLargestPrimeFactorsErdosProblem649Wanted
