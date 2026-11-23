/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Doubling sequences with dense subset sums (Erdős Problem 347)

Erdős Problem 347: is there a sequence `A = {a₁ ≤ a₂ ≤ ⋯}` of integers with `a_{n+1}/a_n → 2` such
that `P(A') = {∑_{n ∈ B} n : B ⊆ A' finite}` has density `1` for every cofinite subsequence `A'`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.DoublingSequenceSubsumDensityErdosProblem347Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #347, https://www.erdosproblems.com/347 (status PROVED
(LEAN)). UnsolvedMath record UM-30006832 (`EP-347`), dataset ulamai/UnsolvedMath v1.8.0.

Terms are positive integers `a i`; a cofinite subsequence is `(a i)_{i ∈ I}` with `I` cofinite, and
`P(A')` sums over finite index sets (repeated values count separately); density is natural density.
formal-conjectures `ErdosProblems/347.lean` sums over the value set `a(I)`, a smaller set, so its
statement implies this one (no code imported).
-/

open Filter Topology

/-- `P(A')` for the subsequence `A' = (a i)_{i ∈ I}`: the sums `∑_{i ∈ T} a i` over finite
`T ⊆ I`. -/
def subsequenceSubsetSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (T : Set ℕ) ⊆ I ∧ s = ∑ i ∈ T, a i}

/-- Erdős Problem 347: there is a non-decreasing sequence of positive integers `a₁ ≤ a₂ ≤ ⋯`
with `a_{n+1} / a_n → 2` such that `P(A')` has natural density `1` for every cofinite
subsequence `A'`. -/
def doublingSequenceDenseSubsums : Prop :=
  ∃ a : ℕ → ℕ, Monotone a ∧ (∀ i, 0 < a i) ∧
    Tendsto (fun i => (a (i + 1) : ℝ) / a i) atTop (𝓝 2) ∧
    ∀ I : Set ℕ, Iᶜ.Finite →
      Tendsto (fun N : ℕ => ((subsequenceSubsetSums a I ∩ Set.Icc 1 N).ncard : ℝ) / N)
        atTop (𝓝 1)

/--
Resolved true: ebarschkis constructed such a sequence in the erdosproblems.com/347 comments
(following ideas of Tao and van Doorn) and formalized the solution in Lean using Aristotle.
erdosproblems.com/347 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#347, https://www.erdosproblems.com/347 (status PROVED (LEAN)); resolution: ebarschkis, solution in
the erdosproblems.com/347 comments (building on ideas of T. Tao and W. van Doorn); Lean
formalization by ebarschkis using Aristotle, github.com/ebarschkis/ErdosProblem,
Problem347/Formalization.lean, erdosproblems.com/347: solved in the affirmative by ebarschkis in the
comments, https://www.erdosproblems.com/347.
-/
public theorem_wanted doublingSequenceDenseSubsums_holds : doublingSequenceDenseSubsums

end MathlibExt.NumberTheory.DoublingSequenceSubsumDensityErdosProblem347Wanted
