/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.ResolutionWidth

/-!
# Tests for resolution size and width

The refutation of `x₀ ∧ ¬x₀` as a tree (size `3`, width `1`) and as a sequence of lines,
widths of clauses with repeated literals, soundness, and a weakening step.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.CNF.ResolutionWidth

open Cslib.Logic.LegacyPL Cslib.Logic.LegacyPL.CNF

/-- The formula `x₀ ∧ ¬x₀`. -/
abbrev contradiction : CNF := [[(0, true)], [(0, false)]]

theorem resolvent_eq_nil : CNFClause.resolvent 0 [(0, true)] [(0, false)] = [] := by decide

/-- The tree-like refutation of `x₀ ∧ ¬x₀`: resolve the two unit clauses. -/
def tree : ResolutionTree contradiction [] :=
  resolvent_eq_nil ▸
    ResolutionTree.resolve 0 (.ax (by simp)) (.ax (by simp)) (by simp) (by simp)

example : contradiction.maxClauseWidth = 1 := by decide

/-- The tree has three lines and width `1`, so the tree-like size-width bound
`2 ^ w ≤ 2 ^ w(φ) · S` reads `2 ≤ 2 · 3` here. -/
example : tree.proofSize = 3 ∧ tree.proofWidth = 1 := by
  refine ⟨rfl, ?_⟩
  decide

example : contradiction.vars.card = 1 := by decide

/-- Widths count distinct literals: `x₀ ∨ x₀ ∨ x₁` has width `2`. -/
example : CNFClause.width [(0, true), (0, true), (1, false)] = 2 := by decide

example : ¬ CNFSat contradiction := tree.not_cnfSat

/-- The refutation as a sequence of lines. -/
example : IsResolutionRefutation contradiction [[(0, true)], [(0, false)], []] := by
  refine ⟨fun i hi => ?_, rfl⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases i with _ | _ | _ | i
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl ⟨0, [(0, true)], by simp, [(0, false)], by simp, by simp, by simp,
      resolvent_eq_nil.symm⟩)
  · omega

example : derivationWidth [[(0, true)], [(0, false)], []] = 1 := by decide

/-- A weakening step: from `x₀` derive `x₀ ∨ x₁`. -/
example : ∃ t : ResolutionTree contradiction [(0, true), (1, true)], t.proofWidth = 2 :=
  ⟨.weaken (C := [(0, true)]) (.ax (by simp)) (by simp), by decide⟩

end CSLibExtTest.Logics.Propositional.CNF.ResolutionWidth
