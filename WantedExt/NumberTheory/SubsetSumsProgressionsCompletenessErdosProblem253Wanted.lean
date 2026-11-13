/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subset sums in every progression without completeness (Erdős Problem 253)

Erdős Problem 253: let `1 ≤ a₁ < a₂ < ⋯` be integers with `aᵢ₊₁ / aᵢ → 1`. If every infinite
arithmetic progression contains infinitely many sums of distinct `aᵢ`, then every sufficiently large
integer is a sum of distinct `aᵢ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SubsetSumsProgressionsCompletenessErdosProblem253Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #253, https://www.erdosproblems.com/253 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006794 (`EP-253`), dataset ulamai/UnsolvedMath v1.8.0.

Indices start at `0`; sums of distinct terms are `∑_{i ∈ S} a i` over finite index sets `S` (the
empty sum is `0`); an infinite progression is `r, r + d, r + 2d, …` with `r ≥ 0` and `d ≥ 1`.
Compared with the formal-conjectures statement `ErdosProblems/253.lean` (equivalent; no code
imported).
-/

open Filter Topology

/-- The sums `∑_{i ∈ S} a i` of finitely many distinct terms of `a` (the empty sum is `0`). -/
def subsetSums (a : ℕ → ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, ∑ i ∈ S, a i = n}

/-- Erdős Problem 253: if `1 ≤ a 0 < a 1 < ⋯` satisfy `a (i + 1) / a i → 1` and every infinite
arithmetic progression `r, r + d, r + 2d, …` (`d ≥ 1`) contains infinitely many sums of distinct
terms, then every sufficiently large integer is a sum of distinct terms. -/
def subsetSumsInAllProgressionsImpliesComplete : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → 1 ≤ a 0 →
    Tendsto (fun i => (a (i + 1) : ℝ) / a i) atTop (𝓝 1) →
    (∀ r d : ℕ, 1 ≤ d → {m ∈ subsetSums a | ∃ j : ℕ, m = r + j * d}.Infinite) →
    ∀ᶠ n in atTop, n ∈ subsetSums a

/--
Resolved false: Cassels constructed a sequence with `aᵢ₊₁ - aᵢ < aᵢ^{1/2 + o(1)}` (so `aᵢ₊₁ / aᵢ →
1`) that has infinitely many terms in every infinite arithmetic progression, while its sums of
distinct terms have density `0`; erdosproblems.com/253 lists the problem as disproved. Source: T. F.
Bloom, Erdős Problems, Problem #253, https://www.erdosproblems.com/253 (status DISPROVED (LEAN));
resolution: J. W. S. Cassels, On the representation of integers as the sums of distinct summands
taken from a fixed set, Acta Sci. Math. (Szeged) 21 (1960), 111-124, erdosproblems.com/253:
disproved by Cassels, a sequence with a_{i+1} - a_i < a_i^{1/2 + o(1)} meeting every infinite
progression infinitely often whose subset sums have density 0, https://www.erdosproblems.com/253.
-/
public theorem_wanted subsetSumsInAllProgressionsImpliesComplete_refuted :
    ¬ subsetSumsInAllProgressionsImpliesComplete

end MathlibExt.NumberTheory.SubsetSumsProgressionsCompletenessErdosProblem253Wanted
