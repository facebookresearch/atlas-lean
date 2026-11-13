/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Divisors from a set versus its reciprocal sum (Erdős Problem 444)

Erdős Problem 444: let `A ⊆ ℕ` be infinite and `d_A(n)` the number of `a ∈ A` dividing `n`. Is it
true that for every `k`, `limsup_{x → ∞} (max_{n < x} d_A(n)) / (∑_{n ∈ A ∩ [1, x)} 1/n)^k = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorCountReciprocalSumErdosProblem444Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #444, https://www.erdosproblems.com/444 (status
PROVED). UnsolvedMath record UM-30006875 (`EP-444`), dataset ulamai/UnsolvedMath v1.8.0.

`d_A(n)` counts positive divisors, the maximum runs over `1 ≤ n < x` (`d_A(0)` would count all of
`A`), and `x` runs over the naturals. The limsup is `∞` iff for every `M` the quotient exceeds `M`
infinitely often, stated without division. `k` runs over the naturals, which covers real `k` since
the reciprocal sum is eventually at least `1` or stays bounded. Compared with the formal-conjectures
statement `ErdosProblems/444.lean` (equivalent to its `EReal`-valued limsup; no code imported).
-/

open scoped Classical in
/-- `d_A(n)`: the number of elements of `A` that divide `n` (positive divisors only). -/
noncomputable def divisorCountIn (A : Set ℕ) (n : ℕ) : ℕ :=
  (n.divisors.filter (· ∈ A)).card

open scoped Classical in
/-- Erdős Problem 444: for every infinite `A ⊆ ℕ` and every `k`,
`limsup_x (max_{1 ≤ n < x} d_A(n)) / (∑_{n ∈ A ∩ [1, x)} 1/n)^k = ∞`. -/
def maxDivisorCountBeatsReciprocalSumPowers : Prop :=
  ∀ A : Set ℕ, A.Infinite → ∀ k : ℕ, ∀ M : ℝ, ∃ᶠ x : ℕ in Filter.atTop,
    M * (∑ n ∈ (Finset.Ico 1 x).filter (· ∈ A), (1 : ℝ) / n) ^ k <
      (((Finset.Ico 1 x).sup (divisorCountIn A) : ℕ) : ℝ)

/--
Resolved true: Erdős and Sárközy proved that the limsup is infinite for every infinite `A` and every
`k`; erdosproblems.com/444 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#444, https://www.erdosproblems.com/444 (status PROVED); resolution: P. Erdős and A. Sárközy, Some
asymptotic formulas on generalized divisor functions. IV, Studia Sci. Math. Hungar. (1980), 467-479,
erdosproblems.com/444: the answer is yes, proved by Erdős and Sárközy.
-/
public theorem_wanted maxDivisorCountBeatsReciprocalSumPowers_holds :
    maxDivisorCountBeatsReciprocalSumPowers

end MathlibExt.NumberTheory.DivisorCountReciprocalSumErdosProblem444Wanted
