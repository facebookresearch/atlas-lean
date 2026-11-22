/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Egyptian fractions for 1 in short intervals (Erdős Problem 286)

Erdős Problem 286: let `k ≥ 2`. Is there an interval `I` of width `(e - 1 + o(1)) k` and integers
`n₁ < ⋯ < n_k ∈ I` with `1 = 1/n₁ + ⋯ + 1/n_k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace MathlibExt.NumberTheory.EgyptianShortIntervalErdosProblem286Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #286, https://www.erdosproblems.com/286 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 33. UnsolvedMath record UM-30006806 (`EP-286`), dataset ulamai/UnsolvedMath v1.8.0.

The `o(1)` is asymptotic in `k`, so the claim concerns all large `k` (for `k = 2` there is no
representation at all). An interval can be enlarged, so "width `(e - 1 + o(1)) k`" is stated as
width at most `(e - 1 + ε) k` for every `ε > 0` and all large `k`. Compared with the
formal-conjectures statement `ErdosProblems/286.lean` (equivalent, stated there with an explicit
`o(1)` function; no code imported).
-/

open Filter

/-- Erdős Problem 286: for every `ε > 0` and all sufficiently large `k` there are integers
`0 < n₁ < ⋯ < n_k` with `1 = 1/n₁ + ⋯ + 1/n_k` lying in an interval of width at most
`(e - 1 + ε) k`, i.e. of width `(e - 1 + o(1)) k`. -/
def unitFractionsInShortInterval : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧
    ∑ n ∈ S, (1 : ℚ) / n = 1 ∧ ∀ m ∈ S, ∀ n ∈ S, (n : ℝ) - m ≤ (Real.exp 1 - 1 + ε) * k

/--
Resolved true: erdosproblems.com/286 records that the answer is yes, proved by Croot [Cr01], and
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #286,
https://www.erdosproblems.com/286 (status PROVED); P. Erdős and R. L. Graham, Old and new problems
and results in combinatorial number theory (1980), p. 33; resolution: E. S. Croot III, On unit
fractions with denominators in short intervals, Acta Arith. (2001), 99-114, erdosproblems.com/286:
answered yes by Croot [Cr01], https://www.erdosproblems.com/286.
-/
public theorem_wanted unitFractionsInShortInterval_holds : unitFractionsInShortInterval

end MathlibExt.NumberTheory.EgyptianShortIntervalErdosProblem286Wanted
