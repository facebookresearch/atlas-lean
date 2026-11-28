/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FillominoDefs
-- Decidability of connectivity on finite graphs, used to check that a block is a polyomino.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace MetaMathlibExt.Complexity.NPComplete.Fillomino

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : FillominoInstance) :
    fillominoDec (bitEncode i) = true ↔ WellFormed i ∧ FillominoFeasible i := by
  simp [fillominoDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : fillominoDec [true] = false := by
  have h : bitDecode (α := FillominoInstance) [true] = none := rfl
  simp [fillominoDec, h]

/-- The row `2 _`: one domino block filled with `2` keeps the given number. -/
example : fillominoDec (bitEncode ([[2, 0]] : FillominoInstance)) = true := by
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, fun _ => 2, fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The row `1 1`: the two cells would form one block of area `2`, or two adjacent blocks of the
same area `1`. -/
example : fillominoDec (bitEncode ([[1, 1]] : FillominoInstance)) = false := by
  have h : ¬ FillominoFeasible [[1, 1]] := by
    rintro ⟨f, block, keep, -, area, apart⟩
    let a : Cell [[1, 1]] := (⟨0, by decide⟩, ⟨0, by decide⟩)
    let b : Cell [[1, 1]] := (⟨0, by decide⟩, ⟨1, by decide⟩)
    have ha : f a = 1 := keep a (by decide)
    have hb : f b = 1 := keep b (by decide)
    by_cases hab : block a = block b
    · have hall : (Finset.univ.filter fun y => block y = block a) = Finset.univ := by
        refine Finset.filter_true_of_mem fun y _ => ?_
        obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := y
        obtain rfl : r = 0 := by have : r < 1 := hr; omega
        obtain rfl | rfl : c = 0 ∨ c = 1 := by have : c < 2 := hc; omega
        · rfl
        · exact hab.symm
      have := area a
      rw [hall, ha] at this
      exact absurd this (by decide)
    · exact apart a b (by decide) hab (by rw [ha, hb])
  simpa [fillominoDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Fillomino
