/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-amenability and transience for free Burnside groups (Kourovka Notebook Problem 7.2)

Kourovka Notebook, Archive of Solved Problems, Problem 7.2 (S. I. Adian): prove that the free
periodic groups `B(m, n)` of odd exponent `n ≥ 665` with `m ≥ 2` generators are non-amenable and
that random walks on these groups do not have the recurrence property.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.GroupTheory.AmenableGroup
public import WantedExt.GroupTheory.BurnsideHigmanEmbeddingKourovka12Problem32Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.FreeBurnsideNonamenableTransientKourovka7Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.2 (S. I.
Adian). UnsolvedMath record UM-00700408 (`KOU-7.2`), dataset ulamai/UnsolvedMath v1.8.0.

`B(m, n)` is `BurnsidePresented n m ∅` from
`WantedExt/GroupTheory/BurnsideHigmanEmbeddingKourovka12Problem32Wanted.lean`: the free group on `m`
generators modulo the normal closure of all `n`-th powers (and no further relators). Amenability is
MathlibExt's Følner-condition `IsAmenable`. The random walk is the simple random walk on `B(m, n)`
with respect to the standard generators `aᵢ^{±1}` (the walk Grigorchuk's cogrowth test and Adian's
paper address): after `k` steps it is at `1` with probability `returnCount m n k / (2m) ^ k`, where
`returnCount m n k` counts the words of length `k` in the `2m` letters that represent `1`. Not
recurrent means transient, that is, the expected number of returns, the sum of these probabilities,
is finite.
-/

open MathlibExt.GroupTheory.BurnsideHigmanEmbeddingKourovka12Problem32Wanted

/-- The number of words of length `k` in the letters `a₁^{±1}, …, a_m^{±1}` that represent `1` in
`B(m, n) = BurnsidePresented n m ∅`; divided by `(2m) ^ k` it is the probability that the simple
random walk on `B(m, n)` with respect to the standard generators is back at `1` after `k` steps. -/
noncomputable def returnCount (m n k : ℕ) : ℕ :=
  Nat.card {w : Fin k → Fin m × Bool //
    (PresentedGroup.mk _ (FreeGroup.mk (List.ofFn w)) : BurnsidePresented n m ∅) = 1}

/-- Kourovka 7.2, first assertion (S. I. Adian): for odd `n ≥ 665` and `m ≥ 2` the free Burnside
group `B(m, n) = BurnsidePresented n m ∅` is not amenable. -/
def freeBurnsideNonamenable : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 665 ≤ n → Odd n → ¬ IsAmenable (BurnsidePresented n m ∅)

/-- Kourovka 7.2, second assertion (S. I. Adian): for odd `n ≥ 665` and `m ≥ 2` the simple random
walk on `B(m, n)` with respect to the standard generators is not recurrent: its return
probabilities are summable. -/
def freeBurnsideRandomWalkTransient : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 665 ≤ n → Odd n →
    Summable fun k : ℕ => (returnCount m n k : ℝ) / (2 * m : ℝ) ^ k

/--
Resolved true: the Kourovka Archive records that Adian (1982) proved both assertions of 7.2; by the
abstract of his paper, `B(m, n)`, `m ≥ 2`, odd `n ≥ 665`, satisfies Grigorchuk's sufficient test (an
upper bound on the growth exponent of the uncancellable words equal to `1`) for the non-amenability
of a group and the transience of its random walk. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 7.2 (S. I. Adian); resolution: S. I. Adian, Random walks on free
periodic groups, Math. USSR-Izv. 21 (1983), 425-434, Kourovka Archive, Problem 7.2: Both assertions
are proved; paper, abstract: B(m, n) with m ≥ 2 and odd n ≥ 665 satisfies Grigorchuk's sufficient
test for transience of the random walk and for non-amenability,
https://doi.org/10.1070/IM1983v021n03ABEH001799.
-/
public theorem_wanted freeBurnsideNonamenable_holds : freeBurnsideNonamenable

/--
Resolved true: the Kourovka Archive records that Adian (1982) proved both assertions of 7.2; by
Grigorchuk's test, which Adian verifies for `B(m, n)`, `m ≥ 2`, odd `n ≥ 665`, the simple random
walk with respect to the standard generators is transient: its return probabilities are summable.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.2 (S. I.
Adian); resolution: S. I. Adian, Random walks on free periodic groups, Math. USSR-Izv. 21 (1983),
425-434, Kourovka Archive, Problem 7.2: Both assertions are proved; paper, abstract: B(m, n) with m
≥ 2 and odd n ≥ 665 satisfies Grigorchuk's sufficient test for transience of the random walk and for
non-amenability, https://doi.org/10.1070/IM1983v021n03ABEH001799.
-/
public theorem_wanted freeBurnsideRandomWalkTransient_holds : freeBurnsideRandomWalkTransient

end MathlibExt.GroupTheory.FreeBurnsideNonamenableTransientKourovka7Problem2Wanted
