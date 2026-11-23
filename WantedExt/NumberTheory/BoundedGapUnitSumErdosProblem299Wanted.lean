/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded-gap sequences avoiding unit sums (Erdős Problem 299)

Erdős Problem 299: is there an infinite sequence `a₁ < a₂ < ⋯` with `a_{i+1} - a_i = O(1)` such that
no finite sum of the `1/a_i` equals `1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.BoundedGapUnitSumErdosProblem299Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #299, https://www.erdosproblems.com/299 (status
DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial
number theory (1980), p. 36. UnsolvedMath record UM-30006814 (`EP-299`), dataset ulamai/UnsolvedMath
v1.8.0.

The terms are positive integers and the finite sums are over sets of distinct indices. Compared with
the formal-conjectures statement `ErdosProblems/299.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 299: there is an infinite sequence `a₁ < a₂ < ⋯` of positive integers with
bounded gaps `a_{i+1} - a_i = O(1)` such that no finite sum of distinct terms `1/a_i` equals `1`. -/
def boundedGapSequenceAvoidsUnitSum : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ (∃ K : ℕ, ∀ i, a (i + 1) - a i ≤ K) ∧
    ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℚ) / a i ≠ 1

/--
Resolved false: a sequence with gaps at most `K` has lower density at least `1/K`, so Bloom's
theorem (Problem 298) gives a finite set of terms with reciprocal sum `1`. erdosproblems.com/299
lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #299,
https://www.erdosproblems.com/299 (status DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old and new
problems and results in combinatorial number theory (1980), p. 36; resolution: T. F. Bloom, On a
density conjecture about unit fractions, arXiv:2112.03726 (2021); formalized in Lean 3 by T. F.
Bloom and B. Mehta (github.com/b-mehta/unit-fractions), erdosproblems.com/299: no such sequence
exists, by the positive solution of Problem 298 (a bounded-gap sequence has positive density),
https://www.erdosproblems.com/299.
-/
public theorem_wanted boundedGapSequenceAvoidsUnitSum_refuted : ¬ boundedGapSequenceAvoidsUnitSum

end MathlibExt.NumberTheory.BoundedGapUnitSumErdosProblem299Wanted
