/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.FK.RandomCluster

open scoped BigOperators
open SimpleGraph

namespace StatMech.Walls







theorem fkc_card_connectedComponent_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
  apply Fintype.card_le_of_surjective G.connectedComponentMk
  intro c
  induction c using ConnectedComponent.ind with
  | _ v => exact ⟨v, rfl⟩



namespace FK

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]








theorem fkc_numClusters_le_card (ω : ConfigSpace (Sym2 V)) :
    numClusters G ω ≤ Fintype.card V := by
  unfold numClusters
  exact fkc_card_connectedComponent_le (openSub G ω)




theorem fkc_numClusters_le_card' (ω : ConfigSpace (Sym2 V)) :
    numClusters G ω ≤ (Finset.univ : Finset V).card := by
  rw [Finset.card_univ]
  exact fkc_numClusters_le_card G ω

end FK

end StatMech.Walls
