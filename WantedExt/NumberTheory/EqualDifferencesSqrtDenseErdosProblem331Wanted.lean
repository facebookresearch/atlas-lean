/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal differences in square-root dense sets (Erdős Problem 331)

Erdős Problem 331: let `A, B ⊆ ℕ` with `|A ∩ {1, …, N}| ≫ N^{1/2}` and `|B ∩ {1, …, N}| ≫ N^{1/2}`
for all large `N`. Are there infinitely many solutions of `a₁ - a₂ = b₁ - b₂ ≠ 0` with `a_i ∈ A`,
`b_i ∈ B`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.NumberTheory.EqualDifferencesSqrtDenseErdosProblem331Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #331, https://www.erdosproblems.com/331 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006826 (`EP-331`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ N^{1/2}` is `≥ c N^{1/2}` for some `c > 0` and all large `N`. Compared with the
formal-conjectures statement `ErdosProblems/331.lean` (equivalent, with the growth written as
`IsBigO`; no code imported).
-/

open Filter

/-- `|A ∩ {1, …, N}| ≫ N^{1/2}` for all large `N`. -/
def HasSqrtGrowth (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * Real.sqrt N ≤ (A ∩ Set.Icc 1 N).ncard

/-- The solutions `(a₁, a₂, b₁, b₂) ∈ A × A × B × B` of `a₁ - a₂ = b₁ - b₂ ≠ 0`. -/
def equalDifferenceSolutions (A B : Set ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {q | q.1 ∈ A ∧ q.2.1 ∈ A ∧ q.2.2.1 ∈ B ∧ q.2.2.2 ∈ B ∧ q.1 ≠ q.2.1 ∧
    (q.1 : ℤ) - q.2.1 = (q.2.2.1 : ℤ) - q.2.2.2}

/-- Erdős Problem 331: if `|A ∩ [1, N]|, |B ∩ [1, N]| ≫ N^{1/2}` for all large `N`, then
`a₁ - a₂ = b₁ - b₂ ≠ 0` has infinitely many solutions with `a_i ∈ A`, `b_i ∈ B`. -/
def infinitelyManyEqualDifferences : Prop :=
  ∀ A B : Set ℕ, HasSqrtGrowth A → HasSqrtGrowth B → (equalDifferenceSolutions A B).Infinite

/--
Resolved false: Ruzsa observed that for `A` the integers with binary digits only in even places and
`B` those with digits only in odd places, both of size `≫ N^{1/2}`, every integer is `a + b` in
exactly one way, so `a₁ + b₂ = a₂ + b₁` forces `a₁ = a₂`. erdosproblems.com/331 lists the problem as
disproved. Source: T. F. Bloom, Erdős Problems, Problem #331, https://www.erdosproblems.com/331
(status DISPROVED (LEAN)); resolution: I. Z. Ruzsa, counterexample recorded on
erdosproblems.com/331, A = integers whose binary digits are nonzero only in even places, B the same
with odd places: both grow like N^{1/2}, and each n ≥ 1 has exactly one representation n = a + b,
https://www.erdosproblems.com/331.
-/
public theorem_wanted infinitelyManyEqualDifferences_refuted : ¬ infinitelyManyEqualDifferences

end MathlibExt.NumberTheory.EqualDifferencesSqrtDenseErdosProblem331Wanted
