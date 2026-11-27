/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SnortOppositionStrategy

open MetaMathlibExt

private def twoEdges : SimpleGraph (Bool × Bool) :=
  SimpleGraph.fromRel fun x y => x.1 = y.1

private instance : DecidableRel twoEdges.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (x.1 = y.1 ∨ y.1 = x.1)))

private def swapEdges : Equiv.Perm (Bool × Bool) :=
  (Equiv.swap false true).prodCongr (Equiv.refl Bool)

private theorem swapEdges_adj : ∀ x y, twoEdges.Adj (swapEdges x) (swapEdges y) ↔ twoEdges.Adj x y :=
  by decide

private def opposition : twoEdges ≃g twoEdges := ⟨swapEdges, swapEdges_adj _ _⟩

-- Swapping the two edge components is an opposition and yields a second-player win.
example : SnortSecondPlayerWins twoEdges :=
  snortSecondPlayerWins_of_isOpposable twoEdges ⟨opposition, by unfold IsOpposition; decide⟩

-- Cross-check the recursive outcome without using the strategy theorem.
example : SnortSecondPlayerWins twoEdges := by
  unfold SnortSecondPlayerWins
  decide

-- The empty graph is opposable by the identity, and the first player cannot move.
example : SnortSecondPlayerWins (⊥ : SimpleGraph (Fin 0)) :=
  snortSecondPlayerWins_of_isOpposable _ ⟨SimpleGraph.Iso.refl, fun v => Fin.elim0 v⟩
