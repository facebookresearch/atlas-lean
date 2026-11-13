/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Eventually greedy best Egyptian underapproximations (Erdős Problem 206)

Erdős Problem 206: for `x > 0` and `n ≥ 1` let `R_n(x)` be the largest sum of `n` distinct unit
fractions below `x`. Is it true that for almost all `x`, for all large `n`, `R_{n+1}(x) = R_n(x) +
1/m` with `m` the least integer not used in `R_n(x)` for which the right side is below `x`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.NumberTheory.EventuallyGreedyEgyptianUnderapproxErdosProblem206Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #206, https://www.erdosproblems.com/206 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006764 (`EP-206`), dataset ulamai/UnsolvedMath v1.8.0.

The eventually greedy property is Kovač's formulation of the question of Erdős and Graham: there are
positive denominators `m 0 < m 1 < ⋯` and `n₀` with `∑_{k < n} 1 / m k = R_n(x)` for all `n ≥ n₀`.
In such a chain the added denominator is the least admissible one, as in the source, since a smaller
admissible denominator would give a larger `(n + 1)`-term underapproximation. The target asks for a
set of positive measure rather than for almost all `x`, so its refutation is Kovač's Theorem 1 (the
eventually greedy `x` form a null set), stronger than a negative answer. Compared with the
formal-conjectures statement `ErdosProblems/206.lean` (there the weaker `¬ ∀ᵐ x`; no code imported).
-/

open MeasureTheory

/-- The sum `∑_{m ∈ S} 1/m` of the unit fractions with denominators in `S`. -/
noncomputable def unitFractionSum (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (1 : ℝ) / m

/-- `q` is the best `n`-term Egyptian underapproximation `R_n(x)` of `x`: `q < x` is a sum of `n`
distinct unit fractions and no sum of `n` distinct unit fractions below `x` is larger. -/
def IsBestUnderapprox (x : ℝ) (n : ℕ) (q : ℝ) : Prop :=
  (∃ S : Finset ℕ, S.card = n ∧ 0 ∉ S ∧ unitFractionSum S = q) ∧ q < x ∧
    ∀ S : Finset ℕ, S.card = n → 0 ∉ S → unitFractionSum S < x → unitFractionSum S ≤ q

/-- `x` has eventually greedy best Egyptian underapproximations (Erdős and Graham; Kovač's
formulation): there are `0 < m 0 < m 1 < ⋯` and `n₀` such that `∑_{k < n} 1 / m k = R_n(x)` for
all `n ≥ n₀`, so from `n₀` on `R_{n+1}(x)` is `R_n(x)` plus one new unit fraction. -/
def HasEventuallyGreedyBestUnderapprox (x : ℝ) : Prop :=
  ∃ m : ℕ → ℕ, StrictMono m ∧ 0 < m 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    IsBestUnderapprox x n (∑ k ∈ Finset.range n, (1 : ℝ) / m k)

/-- Erdős Problem 206, stated for a set of positive measure: the set of `x > 0` with eventually
greedy best Egyptian underapproximations has positive Lebesgue measure. -/
def eventuallyGreedyOnPositiveMeasure : Prop :=
  ∃ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), HasEventuallyGreedyBestUnderapprox x

/--
Resolved false: Kovač proved (Theorem 1) that the set of `x > 0` with eventually greedy best
Egyptian underapproximations has Lebesgue measure zero; so it does not have positive measure, and
almost every `x` fails the property. erdosproblems.com/206 lists the problem as disproved. Source:
T. F. Bloom, Erdős Problems, Problem #206, https://www.erdosproblems.com/206 (status DISPROVED
(LEAN)); resolution: V. Kovač, On eventually greedy best underapproximations by Egyptian fractions,
J. Number Theory 268 (2025), 39-48, arXiv:2406.07218, Theorem 1: the set of positive reals with
eventually greedy best Egyptian underapproximations has Lebesgue measure zero,
https://doi.org/10.1016/j.jnt.2024.09.004.
-/
public theorem_wanted eventuallyGreedyOnPositiveMeasure_refuted :
    ¬ eventuallyGreedyOnPositiveMeasure

end MathlibExt.NumberTheory.EventuallyGreedyEgyptianUnderapproxErdosProblem206Wanted
