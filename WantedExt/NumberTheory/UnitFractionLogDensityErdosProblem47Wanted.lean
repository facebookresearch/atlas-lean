/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unit fractions in sets with large reciprocal sum (Erdős Problem 47)

Erdős Problem 47: if `δ > 0`, `N` is large in terms of `δ` and `A ⊆ {1, …, N}` has `∑_{a ∈ A} 1/a >
δ log N`, must some `S ⊆ A` have `∑_{n ∈ S} 1/n = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.UnitFractionLogDensityErdosProblem47Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #47, https://www.erdosproblems.com/47 (status PROVED
(LEAN)). UnsolvedMath record UM-30006696 (`EP-47`), dataset ulamai/UnsolvedMath v1.8.0.

Sums are real. `S` is a finite subset of `A`; a sum equal to `1` forces `S` nonempty. Compared with
the formal-conjectures statement `ErdosProblems/47.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 47: for every `δ > 0` and all `N` large in terms of `δ`, every
`A ⊆ {1, …, N}` with `∑_{a ∈ A} 1/a > δ log N` has a subset `S` with `∑_{n ∈ S} 1/n = 1`. -/
def logDenseReciprocalSumHasUnitSubsetSum : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    δ * Real.log N < ∑ a ∈ A, (1 : ℝ) / a → ∃ S ⊆ A, ∑ n ∈ S, (1 : ℝ) / n = 1

/--
Resolved true: Bloom (Theorem 3) proved that `∑_{n ∈ A} 1/n ≥ C (log log log N / log log N) log N`
already forces a subset with reciprocal sum `1`, and this threshold is below `δ log N` for large
`N`; Liu and Sawhney improved the threshold to `(log N) ^ (4/5 + o(1))`. Source: T. F. Bloom, Erdős
Problems, Problem #47, https://www.erdosproblems.com/47 (status PROVED (LEAN)); resolution: T. F.
Bloom, On a density conjecture about unit fractions, arXiv:2112.03726 (2021), Theorem 3: for an
absolute constant C, every A ⊆ {1, …, N} with ∑_{n ∈ A} 1/n ≥ C (log log log N / log log N) log N
has a subset S with ∑_{n ∈ S} 1/n = 1; erdosproblems.com/47, https://arxiv.org/abs/2112.03726.
-/
public theorem_wanted logDenseReciprocalSumHasUnitSubsetSum_holds :
    logDenseReciprocalSumHasUnitSubsetSum

end MathlibExt.NumberTheory.UnitFractionLogDensityErdosProblem47Wanted
