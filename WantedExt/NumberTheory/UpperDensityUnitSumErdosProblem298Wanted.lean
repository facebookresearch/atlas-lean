/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unit sums in sets of positive density (Erdős Problem 298)

Erdős Problem 298: does every `A ⊆ ℕ` of positive density contain a finite `S ⊂ A` with `∑_{n ∈ S}
1/n = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.UpperDensityUnitSumErdosProblem298Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #298, https://www.erdosproblems.com/298 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980). UnsolvedMath record UM-30006813 (`EP-298`), dataset ulamai/UnsolvedMath v1.8.0.

Positive density is read as positive upper density (`δ N ≤ |A ∩ [1, N]|` for infinitely many `N`),
the weaker hypothesis that Bloom proves, so the statement is the strongest form; `A` is a set of
positive integers. Compared with the formal-conjectures statement `ErdosProblems/298.lean`
(equivalent; no code imported).
-/

open Filter

/-- Erdős Problem 298: every set `A` of positive integers of positive upper density contains a
finite `S` with `∑_{n ∈ S} 1/n = 1`. -/
def positiveUpperDensityHasUnitSum : Prop :=
  ∀ A : Set ℕ, 0 ∉ A →
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in atTop, δ * N ≤ (A ∩ Set.Icc 1 N).ncard) →
      ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

/--
Resolved true: Bloom proved that every set of positive integers of positive upper density contains a
finite `S` with `∑_{n ∈ S} 1/n = 1` (formalized in Lean 3 by Bloom and Mehta). erdosproblems.com/298
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #298,
https://www.erdosproblems.com/298 (status PROVED (LEAN)); P. Erdős and R. L. Graham, Old and new
problems and results in combinatorial number theory (1980); resolution: T. F. Bloom, On a density
conjecture about unit fractions, arXiv:2112.03726 (2021); formalized in Lean 3 by T. F. Bloom and B.
Mehta (github.com/b-mehta/unit-fractions), abstract: any A ⊂ ℕ of positive upper density contains a
finite S ⊂ A with ∑_{n∈S} 1/n = 1, answering the Erdős-Graham question,
https://arxiv.org/abs/2112.03726.
-/
public theorem_wanted positiveUpperDensityHasUnitSum_holds : positiveUpperDensityHasUnitSum

end MathlibExt.NumberTheory.UpperDensityUnitSumErdosProblem298Wanted
