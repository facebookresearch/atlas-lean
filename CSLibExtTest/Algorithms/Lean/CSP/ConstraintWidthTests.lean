/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.CSP.ConstraintWidth

/-! # Tests for ordinary constraint-graph width -/

namespace Cslib.Algorithms.Lean.ArcConsistency

private def pathWithIsolate : BinaryCSP (Fin 4) Unit where
  arcs := [(0, 1), (0, 1), (1, 0), (2, 1), (1, 1), (3, 3)]
  allowed := fun x y _ _ => x == 3 && y == 0

private def goodOrder : Fin 4 ≃ Fin (Fintype.card (Fin 4)) :=
  finCongr (Fintype.card_fin 4).symm

private def badOrder : Fin 4 ≃ Fin (Fintype.card (Fin 4)) :=
  (Equiv.swap 1 2).trans goodOrder

-- A one-way listed arc gives both adjacencies even though it allows no value pair.
example : pathWithIsolate.constraintGraph.Adj 1 2 ∧ pathWithIsolate.constraintGraph.Adj 2 1 := by
  decide

-- An unlisted pair does not become an edge, and a listed loop is discarded.
example : ¬pathWithIsolate.constraintGraph.Adj 3 0 ∧ ¬pathWithIsolate.constraintGraph.Adj 1 1 := by
  decide

-- The forward duplicates and reverse copy contribute only one earlier neighbor.
example : pathWithIsolate.vertexWidth goodOrder 1 = 1 := by decide
example : pathWithIsolate.vertexWidth badOrder 1 = 2 := by decide
example : pathWithIsolate.vertexWidth badOrder 3 = 0 := by decide
example : pathWithIsolate.orderWidth goodOrder = 1 := by decide
example : pathWithIsolate.orderWidth badOrder = 2 := by decide

private theorem pathWithIsolate_isAcyclic : pathWithIsolate.constraintGraph.IsAcyclic := by
  apply (SimpleGraph.isAcyclic_pathGraph 4).anti
  intro x y
  fin_cases x <;> fin_cases y <;> decide

example : pathWithIsolate.constraintWidth = 1 := by
  have hle := pathWithIsolate.constraintWidth_le_one_of_isAcyclic pathWithIsolate_isAcyclic
  have hne : pathWithIsolate.constraintWidth ≠ 0 := by
    intro hz
    have h : pathWithIsolate.constraintGraph.Adj 0 1 := by decide
    rw [pathWithIsolate.constraintWidth_eq_zero_iff.mp hz] at h
    exact (SimpleGraph.bot_adj _ _).mp h
  omega

private def loopsOnly : BinaryCSP (Fin 4) Unit where
  arcs := [(0, 0), (2, 2), (2, 2)]
  allowed := fun _ _ _ _ => true

example : loopsOnly.orderWidth badOrder = 0 := by decide
example : loopsOnly.constraintWidth = 0 := by
  apply loopsOnly.constraintWidth_eq_zero_iff.mpr
  ext x y
  fin_cases x <;> fin_cases y <;> decide

private def noVariables : BinaryCSP (Fin 0) Unit where
  arcs := []
  allowed := fun _ _ _ _ => false

example : noVariables.orderWidth (finCongr (Fintype.card_fin 0).symm) = 0 := by decide
example : noVariables.constraintWidth = 0 := by
  apply noVariables.constraintWidth_eq_zero_iff.mpr
  ext x
  exact Fin.elim0 x

end Cslib.Algorithms.Lean.ArcConsistency
