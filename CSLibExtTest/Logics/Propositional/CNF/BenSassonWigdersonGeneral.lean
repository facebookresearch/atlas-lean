/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Propositional.CNF.BenSassonWigdersonGeneral
import Mathlib.Tactic.IntervalCases

namespace CSLibExtTest.Logics.Propositional.CNF.BenSassonWigdersonGeneral

open Cslib.Logic.LegacyPL Cslib.Logic.LegacyPL.CNF
open MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted (refutation_narrow)

/-- **The one-clause refutation.** The empty clause alone refutes `[[]]`. -/
private theorem one_refutation : IsResolutionRefutation [[]] [[]] := by
  refine ⟨?_, rfl⟩
  intro i hi
  have hi' : i < 1 := hi
  interval_cases i
  exact Or.inl (by simp)

/-- **The general bound applied to the one-clause refutation.** The bound
forces the resulting refutation to have width zero. -/
example : ∃ π' : List CNFClause, IsResolutionRefutation [[]] π' ∧
    derivationWidth π' = 0 := by
  obtain ⟨c, -, hall⟩ := refutation_narrow
  obtain ⟨π', href', hw'⟩ := hall [[]] [[]] one_refutation
  refine ⟨π', href', ?_⟩
  have hbound : (derivationWidth π' : ℝ) ≤ 0 := by
    have h1 : CNF.maxClauseWidth [[]] = 0 := by decide
    have h2 : (CNF.vars [[]]).card = 0 := by decide
    have h3 : ([[]] : List CNFClause).length = 1 := rfl
    rw [h1, h2, h3] at hw'
    simpa using hw'
  exact Nat.le_zero.mp (by exact_mod_cast hbound)

/-- **The two-variable unsatisfiable formula.** All four sign combinations. -/
private def fourClauses : CNF :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
    [(0, false), (1, true)], [(0, false), (1, false)]]

/-- **Its explicit seven-line refutation.** Resolve on variable `1` twice,
then on variable `0`. -/
private def sevenLines : List CNFClause :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
    [(0, false), (1, true)], [(0, false), (1, false)], [(0, false), (0, false)], []]

/-- **The explicit refutation is a resolution refutation.** -/
private theorem seven_refutation : IsResolutionRefutation fourClauses sevenLines := by
  refine ⟨?_, rfl⟩
  intro i hi
  have hlen : sevenLines.length = 7 := rfl
  rw [hlen] at hi
  interval_cases i
  · show IsResolutionStep fourClauses [] [(0, true), (1, true)]
    exact Or.inl (by decide)
  · show IsResolutionStep fourClauses [[(0, true), (1, true)]] [(0, true), (1, false)]
    exact Or.inl (by decide)
  · show IsResolutionStep fourClauses
      [[(0, true), (1, true)], [(0, true), (1, false)]] [(0, true), (0, true)]
    exact Or.inr (Or.inl ⟨1, [(0, true), (1, true)], by decide,
      [(0, true), (1, false)], by decide, by decide, by decide, rfl⟩)
  · show IsResolutionStep fourClauses
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)]]
      [(0, false), (1, true)]
    exact Or.inl (by decide)
  · show IsResolutionStep fourClauses
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
        [(0, false), (1, true)]] [(0, false), (1, false)]
    exact Or.inl (by decide)
  · show IsResolutionStep fourClauses
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
        [(0, false), (1, true)], [(0, false), (1, false)]] [(0, false), (0, false)]
    exact Or.inr (Or.inl ⟨1, [(0, false), (1, true)], by decide,
      [(0, false), (1, false)], by decide, by decide, by decide, rfl⟩)
  · show IsResolutionStep fourClauses
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
        [(0, false), (1, true)], [(0, false), (1, false)], [(0, false), (0, false)]] []
    exact Or.inr (Or.inl ⟨0, [(0, true), (0, true)], by decide,
      [(0, false), (0, false)], by decide, by decide, by decide, rfl⟩)

/-- **The general bound applied to a nontrivial refutation.** The constant
from `refutation_narrow` gives a refutation of width at most
`2 + c * √(2 ln 7)`. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ π' : List CNFClause,
    IsResolutionRefutation fourClauses π' ∧
      (derivationWidth π' : ℝ) ≤
        2 + c * Real.sqrt (2 * Real.log 7) := by
  obtain ⟨c, hc, hall⟩ := refutation_narrow
  obtain ⟨π', href', hw'⟩ := hall fourClauses sevenLines seven_refutation
  refine ⟨c, hc, π', href', ?_⟩
  have h1 : fourClauses.maxClauseWidth = 2 := by decide
  have h2 : fourClauses.vars.card = 2 := by decide
  have h3 : sevenLines.length = 7 := rfl
  rw [h1, h2, h3] at hw'
  simpa using hw'

end CSLibExtTest.Logics.Propositional.CNF.BenSassonWigdersonGeneral
