/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gaps between smooth numbers over infinitely many primes (Erdős Problem 240)

Erdős Problem 240 (Wintner): is there an infinite set of primes `P` such that, if `a₁ < a₂ < ⋯` are
the integers divisible only by primes in `P`, then `aᵢ₊₁ - aᵢ → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SmoothNumberGapsInfinitePrimesErdosProblem240Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #240, https://www.erdosproblems.com/240 (status
PROVED). UnsolvedMath record UM-30006788 (`EP-240`), dataset ulamai/UnsolvedMath v1.8.0.

The integers are the `n ≥ 1` with all prime factors in `P` (including `1`), enumerated by `Nat.nth`;
the set is infinite because `P` is nonempty.
-/

open Filter

/-- `n ≥ 1` is divisible only by primes in `P`. -/
def IsSmoothOver (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, p ∈ P

/-- Erdős Problem 240: there is an infinite set `P` of primes such that the integers
`a₁ < a₂ < ⋯` divisible only by primes in `P` satisfy `aᵢ₊₁ - aᵢ → ∞`. -/
def infinitePrimeSetSmoothGapsTendToInfinity : Prop :=
  ∃ P : Set ℕ, P.Infinite ∧ (∀ p ∈ P, p.Prime) ∧
    Tendsto (fun i => Nat.nth (IsSmoothOver P) (i + 1) - Nat.nth (IsSmoothOver P) i) atTop atTop

/--
Resolved true: Tijdeman proved that for every `ε > 0` there is an infinite set of primes `P` for
which `aᵢ₊₁ - aᵢ ≫ aᵢ^{1 - ε}`; erdosproblems.com/240 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #240, https://www.erdosproblems.com/240 (status PROVED); resolution:
R. Tijdeman, On integers with many small prime factors, Compositio Math. 26 (1973), 319-330,
erdosproblems.com/240: Tijdeman proved that for every ε > 0 there is an infinite set of primes P
with a_{i+1} - a_i ≫ a_i^{1-ε}, http://www.numdam.org/item/CM_1973__26_3_319_0/.
-/
public theorem_wanted infinitePrimeSetSmoothGapsTendToInfinity_holds :
    infinitePrimeSetSmoothGapsTendToInfinity

end MathlibExt.NumberTheory.SmoothNumberGapsInfinitePrimesErdosProblem240Wanted
