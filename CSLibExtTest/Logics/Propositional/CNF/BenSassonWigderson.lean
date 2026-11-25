/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Propositional.CNF.BenSassonWigderson

namespace CSLibExtTest.Logics.Propositional.CNF.BenSassonWigderson

open Cslib.Logic.LegacyPL Cslib.Logic.LegacyPL.CNF
open MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted (tree_refutation_narrow)

-- The one-line refutation has size one and input width zero.
example : ∃ π : List CNFClause, IsResolutionRefutation [[]] π ∧ 2 ^ derivationWidth π ≤ 1 := by
  let t : ResolutionTree [[]] [] := .ax (by simp)
  have hw : maxClauseWidth [[]] = 0 := by decide
  have ht : t.proofSize = 1 := rfl
  simpa only [hw, ht, Nat.pow_zero, Nat.mul_one] using tree_refutation_narrow [[]] t

private def fourClauses : CNF :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
    [(0, false), (1, true)], [(0, false), (1, false)]]

-- Resolving on variable 1 makes repeated pivot literals for the resolution on variable 0.
-- The two branches have different sizes, and a final weakening preserves the empty clause.
private def fourClauseTree : ResolutionTree fourClauses [] := by
  have left : ResolutionTree fourClauses [(0, true), (0, true)] :=
    .resolve (C := [(0, true), (1, true)]) (D := [(0, true), (1, false)]) 1
      (.ax (by simp [fourClauses])) (.ax (by simp [fourClauses])) (by simp) (by simp)
  have right : ResolutionTree fourClauses [(0, false), (0, false)] :=
    .resolve (C := [(0, false), (1, true)]) (D := [(0, false), (1, false)]) 1
      (.ax (by simp [fourClauses])) (.ax (by simp [fourClauses])) (by simp) (by simp)
  have larger : ResolutionTree fourClauses [(0, true), (0, true), (0, true)] :=
    .weaken left (by simp)
  have resolved : ResolutionTree fourClauses [] := .resolve 0 larger right (by simp) (by simp)
  exact .weaken resolved (List.Subset.refl _)

example : ∃ π : List CNFClause, IsResolutionRefutation fourClauses π ∧
    2 ^ derivationWidth π ≤ 36 := by
  have hwidth : fourClauses.maxClauseWidth = 2 := by decide
  have hsize : fourClauseTree.proofSize = 9 := rfl
  have hbound : (2 : ℕ) ^ 2 * 9 = 36 := rfl
  simpa only [hwidth, hsize, hbound] using tree_refutation_narrow fourClauses fourClauseTree

end CSLibExtTest.Logics.Propositional.CNF.BenSassonWigderson
