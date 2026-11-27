/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.SmoothPrimeGaps
public import WantedExt.NumberTheory.PrimeGapBoundsHypotheses

/-!
# Smooth gaps between primes

Statements from Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao
Sieve*, INTEGERS 25 (2025), Article A44 (arXiv:2403.19696).

An integer is `y`-smooth when all its prime factors are at most `y`; for a
nonzero natural number `d` this is `d ∈ Nat.smoothNumbers (y + 1)` (Mathlib's
`smoothNumbers n` uses the strict bound `p < n`). Tuples of integers are finite
sets of distinct integers; admissibility is `IsAdmissibleFinset`, the `Finset` form of
`IsHardyLittlewoodAdmissible` (`isHardyLittlewoodAdmissible_iff_isAdmissibleFinset`).
The Elliott-Halberstam conjecture is WantedExt's `Polymath8b.ElliottHalberstam` (the
dyadic formulation for every level `θ < 1`), the hypothesis already used for Maynard's
conditional bound in `WantedExt/NumberTheory/PrimeGapBoundsWanted.lean`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many prime pairs with $47$-smooth difference.** There are infinitely many pairs
of primes $p > q$ such that every prime factor of $p - q$ is at most $47$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 1 (`integers-2025-A44-thm-1`). -/
public theorem_wanted infinite_prime_pairs_smooth_47_gap :
    {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.2 < pq.1 ∧
      pq.1 - pq.2 ∈ Nat.smoothNumbers 48}.Infinite

/-- **Maynard–Tao theorem.** For every natural number $m \ge 2$ there is a natural number $k$
such that for every admissible finite set $H$ of at least $k$ integers there are infinitely many
integers $n$ for which $n + h$ is a (positive) prime for at least $m$ elements $h \in H$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 2 (`integers-2025-A44-thm-2`), citing
J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015). -/
public theorem_wanted maynard_tao_admissible_tuples (m : ℕ) (hm : 2 ≤ m) :
    ∃ k : ℕ, ∀ H : Finset ℤ, IsAdmissibleFinset H → k ≤ H.card →
      {n : ℤ | m ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite

/-- **Prime $m$-tuples with smooth gaps.** Let $m \ge 2$ and $k$ be natural numbers such that
every admissible finite set $H$ of at least $k$ integers has infinitely many integers $n$ for
which $n + h$ is a (positive) prime for at least $m$ elements $h \in H$. Then there are
infinitely many $m$-tuples of primes $p_1 < p_2 < \dots < p_m$ such that for all $j < i$ every
prime factor of $p_i - p_j$ is at most $k$.

Equivalently, every gap is $y$-smooth for $y$ the largest prime at most $k$; the paper applies
this with the admissible values $k_m$ of the Maynard–Tao theorem listed in its Table 1.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 3 (`integers-2025-A44-thm-3`). -/
public theorem_wanted infinite_prime_tuples_smooth_gaps (m k : ℕ) (hm : 2 ≤ m)
    (hk : ∀ H : Finset ℤ, IsAdmissibleFinset H → k ≤ H.card →
      {n : ℤ | m ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite) :
    {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
      ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)}.Infinite

/-- **Prime pairs with $5$-smooth difference under Elliott–Halberstam.** If the
Elliott–Halberstam conjecture holds, then there are infinitely many pairs of primes $p > q$ such
that every prime factor of $p - q$ is at most $5$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 4 (`integers-2025-A44-thm-4`). -/
public theorem_wanted infinite_prime_pairs_smooth_5_gap_of_elliottHalberstam :
    WantedExt.NumberTheory.Polymath8b.ElliottHalberstam →
    {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.2 < pq.1 ∧
      pq.1 - pq.2 ∈ Nat.smoothNumbers 6}.Infinite

end

end MetaMathlibExt
