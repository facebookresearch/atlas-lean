/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.JoinEdgeCovers
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Tests for query edge covers -/

namespace Cslib.Databases.JoinEdgeCoversTests

private def cycle : Expr (Fin 3) (Fin 3) ℕ := .join (.rel 0) (.join (.rel 1) (.rel 2))

-- The triangle values are for the relational expression itself.
example : cycle.edgeCoverNumbers? (fun i => {i, i + 1}) = some (2, 3 / 2) := by
  have h : cycle.fullJoinRelations? = some Finset.univ := by decide
  simp only [Expr.edgeCoverNumbers?, Expr.joinHypergraph?, h, Option.map_some]
  exact congrArg some (Prod.ext JoinHypergraph.triangle_coverNumbers.1
    JoinHypergraph.triangle_coverNumbers.2)

-- A repeated use of one name coalesces, but two names over the same heading do not.
-- Attribute `false` does not occur and is not a vertex, despite inhabiting the ambient type.
private def repeated : Expr Bool Bool Unit := .join (.rel false) (.join (.rel true) (.rel false))

example : ((repeated.joinHypergraph? fun _ => {true}).map fun H =>
    (H.relations.card, H.vertices)) = some (2, {true}) := by decide

-- Projecting away even one triangle attribute leaves the full-join fragment.
example : (Expr.project {0, 1} cycle).edgeCoverNumbers? (fun i => {i, i + 1}) = none := rfl

-- A nullary relation has an edge but no vertices; there is also an empty named family.
example : (((Expr.rel true : Expr Bool Bool Unit).joinHypergraph? fun _ => ∅).map fun H =>
    (H.relations.card, H.vertices)) = some (1, ∅) := by decide

example : (JoinHypergraph.mk (∅ : Finset Bool) (fun _ => {true})).vertices = ∅ := by decide

-- Both minima are zero for any family with empty vertex union, including the two cases above.
example {N A : Type*} [DecidableEq A] (H : JoinHypergraph N A) (h : H.vertices = ∅) :
    H.edgeCoverNumber = 0 ∧ H.fractionalEdgeCoverNumber = 0 := by
  constructor
  · apply H.isLeast_edgeCoverNumber.unique
    exact ⟨⟨∅, by simp [JoinHypergraph.IsEdgeCover, h], rfl⟩, fun _ _ => Nat.zero_le _⟩
  · apply H.isLeast_fractionalEdgeCoverNumber.unique
    refine ⟨⟨0, ⟨le_rfl, by simp [h]⟩, by simp⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact Finset.sum_nonneg fun r _ => hw.1 r

end Cslib.Databases.JoinEdgeCoversTests
