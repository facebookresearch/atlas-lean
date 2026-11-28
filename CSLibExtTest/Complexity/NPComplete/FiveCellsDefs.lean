/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FiveCellsDefs
-- Decidability of connectivity on finite graphs, used to check that a block is connected.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace MetaMathlibExt.Complexity.NPComplete.FiveCells

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : FiveCellsInstance) :
    fiveCellsDec (bitEncode i) = true ↔ WellFormed i ∧ FiveCellsFeasible i := by
  simp [fiveCellsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : fiveCellsDec [true] = false := by
  have h : bitDecode (α := FiveCellsInstance) [true] = none := rfl
  simp [fiveCellsDec, h]

/-- The row `3 _ 2 _ _` (codes `4 0 3 0 0`) as one block of five cells: the end cell has one
neighbour in its block and three lines around it, the middle cell two of each. -/
example : fiveCellsDec (bitEncode ([[4, 0, 3, 0, 0]] : FiveCellsInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ => 0, ?_, ?_, ?_⟩
  all_goals simp only
  all_goals decide

/-- The row `0 _ _ _ _` (codes `1 0 0 0 0`): a number `0` needs four neighbours in its own block,
but the end cell of a row has only one neighbour. -/
example : fiveCellsDec (bitEncode ([[1, 0, 0, 0, 0]] : FiveCellsInstance)) = false := by
  have h : ¬ FiveCellsFeasible [[1, 0, 0, 0, 0]] := by
    rintro ⟨block, -, -, clue⟩
    let x : Fin (rows [[1, 0, 0, 0, 0]]) × Fin (cols [[1, 0, 0, 0, 0]]) :=
      (⟨0, by decide⟩, ⟨0, by decide⟩)
    have hx := clue x (by decide)
    rw [Finset.filter_congr_decidable] at hx
    have hle : (Finset.univ.filter fun y =>
        (Grid [[1, 0, 0, 0, 0]]).Adj x y ∧ block y = block x).card ≤
        (Finset.univ.filter fun y => (Grid [[1, 0, 0, 0, 0]]).Adj x y).card :=
      Finset.card_le_card fun y hy => by
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, hy.2.1⟩
    have hone : (Finset.univ.filter fun y => (Grid [[1, 0, 0, 0, 0]]).Adj x y).card = 1 := by
      decide
    have : cell [[1, 0, 0, 0, 0]] x = 1 := by decide
    omega
  simpa [fiveCellsDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.FiveCells
