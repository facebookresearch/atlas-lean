/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Compaction

@[expose] public section

namespace Cslib.Logic.PL.CNFTest

open CNF

example : CNF.modelCount [] = 1 := by
  exact CNF.modelCount_nil

private def sparse : CNF :=
  [[(7, true), (100, false)], [(7, true)]]

private theorem compact_eq_source (formula : CNF) :
    formula.compact = formula.map fun clause => clause.map fun literal =>
      (((formula.flatMap fun C => C.map Prod.fst).dedup.idxOf literal.1), literal.2) := by
  rfl

example : sparse.compact = sparse.map fun clause => clause.map fun literal =>
    (((sparse.flatMap fun C => C.map Prod.fst).dedup.idxOf literal.1), literal.2) := by
  exact compact_eq_source sparse

example : sparse.compact = [[(1, true), (0, false)], [(1, true)]] := by
  decide

example : sparse.compact.vars = Finset.range sparse.vars.card := by
  exact CNF.vars_compact sparse

example : sparse.compact.length = sparse.length := by
  exact CNF.length_compact sparse

example : sparse.compact.map List.length = sparse.map List.length := by
  exact CNF.clauseLengths_compact sparse

example : (∀ clause ∈ sparse.compact, clause.length ≤ 2) ↔
    ∀ clause ∈ sparse, clause.length ≤ 2 := by
  exact CNF.boundedClauseLength_compact_iff sparse 2

private theorem kCNF_schema_compact_iff (formula : CNF) (k : Nat) :
    ((∀ clause ∈ formula.compact, clause.length ≤ k) ∧ formula.compact.Nodup) ↔
      (∀ clause ∈ formula, clause.length ≤ k) ∧ formula.Nodup := by
  rw [CNF.boundedClauseLength_compact_iff, CNF.nodup_compact_iff]

example : sparse.compact.Nodup := by
  exact CNF.nodup_compact_iff sparse |>.mpr (by decide)

private def duplicateClauses : CNF := [[(7, true)], [(7, true)]]

example : ¬duplicateClauses.compact.Nodup := by
  rw [CNF.nodup_compact_iff]
  decide

example :
    ((∀ clause ∈ sparse.compact, clause.length ≤ 2) ∧ sparse.compact.Nodup) ↔
      (∀ clause ∈ sparse, clause.length ≤ 2) ∧ sparse.Nodup := by
  exact kCNF_schema_compact_iff sparse 2

example (assignment : Nat → Bool) :
    sparse.compact.Satisfies assignment ↔
      sparse.Satisfies fun x => assignment ([100, 7].idxOf x) := by
  simpa [sparse] using CNF.satisfies_compact_iff sparse assignment

example : sparse.compact.modelCount = sparse.modelCount := by
  exact CNF.modelCount_compact sparse

noncomputable example (formula : CNF) (N : Nat) (hvars : ∀ x ∈ formula.vars, x < N) :
    Nat.card {assignment : Fin N → Bool //
      formula.Satisfies fun x => if h : x < N then assignment ⟨x, h⟩ else false} =
      2 ^ (N - formula.vars.card) * formula.modelCount := by
  classical
  exact CNF.card_satisfying_fin formula N hvars

example : ¬∀ x ∈ CNF.vars ([[(4, true)]] : CNF), x < 4 := by
  simp

example : CNF.modelCount ([[]] : CNF) = 0 := by decide

example : CNF.modelCount ([[(7, true), (7, true)]] : CNF) = 1 := by decide

example : CNF.modelCount ([[(7, true), (7, false)]] : CNF) = 2 := by decide

example : CNF.modelCount ([[(7, true)], [(7, false)]] : CNF) = 0 := by decide

example : sparse.modelCount = 2 := by decide

private def oneOr : CNF := [[(0, true), (3, true)]]

example : oneOr.modelCount = 3 := by decide

example : Nat.card {assignment : Fin 4 → Bool //
    oneOr.Satisfies fun x => if h : x < 4 then assignment ⟨x, h⟩ else false} = 12 := by
  rw [CNF.card_satisfying_fin oneOr 4 (by simp [oneOr])]
  decide

end Cslib.Logic.PL.CNFTest
