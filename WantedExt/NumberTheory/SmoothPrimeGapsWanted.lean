/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import Mathlib.NumberTheory.SmoothNumbers
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

/-- A tuple `H` is difference `y`-smooth if `h_i - h_j` is `y`-smooth for all
distinct `h_i, h_j ∈ H`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 3. -/
def IsDifferenceSmooth (y : ℕ) (H : Finset ℤ) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (a - b).natAbs ∈ Nat.smoothNumbers (y + 1)

/-- A one-element tuple is difference `y`-smooth for every `y`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 3. -/
theorem isDifferenceSmooth_singleton (y : ℕ) (a : ℤ) : IsDifferenceSmooth y {a} := by
  intro b hb c hc hbc
  rw [Finset.mem_singleton] at hb hc
  exact absurd (hb.trans hc.symm) hbc

/-- Infinitely many pairs of primes `p > q` have `47`-smooth difference `p - q`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 1 (`integers-2025-A44-thm-1`). -/
public theorem_wanted infinite_prime_pairs_smooth_47_gap :
    {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.2 < pq.1 ∧
      pq.1 - pq.2 ∈ Nat.smoothNumbers 48}.Infinite

/-- Maynard–Tao theorem: for every `m ≥ 2` there is `k_m` such that for every
admissible tuple `H` with at least `k_m` elements there are infinitely many
integers `n` with `n + h` a (positive) prime for at least `m` elements `h ∈ H`.
The historical remarks on admissible values of `k_2` and the bound
`k_m < c m² e^{4m}` are not included.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 2 (`integers-2025-A44-thm-2`), citing
J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015). -/
public theorem_wanted maynard_tao_admissible_tuples (m : ℕ) (hm : 2 ≤ m) :
    ∃ k : ℕ, ∀ H : Finset ℤ, IsAdmissibleFinset H → k ≤ H.card →
      {n : ℤ | m ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite

/-- Prime `m`-tuples with smooth gaps: if `k` is an admissible value of `k_m` in
the Maynard–Tao theorem (every admissible tuple with at least `k` elements has
infinitely many shifts containing `m` primes), then there are infinitely many
increasing `m`-tuples of primes `p_1 < ⋯ < p_m` all of whose gaps `p_i - p_j` are
`y_m`-smooth, `y_m` the largest prime `≤ k`. The gaps are stated as
`k`-smooth, which is the same condition; the paper applies this with the values
`k_m` of its Table 1 and remarks.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 3 (`integers-2025-A44-thm-3`). -/
public theorem_wanted infinite_prime_tuples_smooth_gaps (m k : ℕ) (hm : 2 ≤ m)
    (hk : ∀ H : Finset ℤ, IsAdmissibleFinset H → k ≤ H.card →
      {n : ℤ | m ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite) :
    {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
      ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)}.Infinite

/-- Assuming the Elliott-Halberstam conjecture, there are infinitely many pairs of
primes `p > q` whose difference `p - q` is `5`-smooth.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 4 (`integers-2025-A44-thm-4`). -/
public theorem_wanted infinite_prime_pairs_smooth_5_gap_of_elliottHalberstam :
    WantedExt.NumberTheory.Polymath8b.ElliottHalberstam →
    {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.2 < pq.1 ∧
      pq.1 - pq.2 ∈ Nat.smoothNumbers 6}.Infinite

/-- For every `k` there is an admissible `k`-tuple of integers that is
difference `k`-smooth.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 5 (`integers-2025-A44-thm-5`). -/
public theorem_wanted exists_admissible_differenceSmooth (k : ℕ) :
    ∃ H : Finset ℤ, H.card = k ∧ IsAdmissibleFinset H ∧ IsDifferenceSmooth k H

/-- An admissible `k`-tuple, `k ≥ 2`, is not difference `ℓ`-smooth for any
`ℓ < z_k`, `z_k` the largest prime `≤ k`; equivalently, for every prime
`z ≤ k` and every `ℓ < z`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Proposition 1 (`integers-2025-A44-prop-1`). -/
public theorem_wanted not_isDifferenceSmooth_of_isAdmissibleFinset (H : Finset ℤ)
    (hk : 2 ≤ H.card) (hH : IsAdmissibleFinset H) (z : ℕ) (hz : z.Prime) (hzk : z ≤ H.card)
    (ℓ : ℕ) (hℓ : ℓ < z) : ¬ IsDifferenceSmooth ℓ H

end

end MetaMathlibExt
