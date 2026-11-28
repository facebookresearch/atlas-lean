/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EyeWitlessDefs

namespace MetaMathlibExt.Complexity.NPComplete.EyeWitless

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : EyeWitlessInstance) :
    eyeWitlessDec (bitEncode i) = true ↔ WellFormed i ∧ EyeWitlessFeasible i := by
  simp [eyeWitlessDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : eyeWitlessDec [true] = false := by
  have h : bitDecode (α := EyeWitlessInstance) [true] = none := rfl
  simp [eyeWitlessDec, h]

/-- The two diagonal eyes of a `2 × 2` grid. -/
private abbrev diag : EyeWitlessInstance := [[1, 0], [0, 1]]

private abbrev c00 : Fin (rows diag) × Fin (cols diag) := (⟨0, by decide⟩, ⟨0, by decide⟩)
private abbrev c01 : Fin (rows diag) × Fin (cols diag) := (⟨0, by decide⟩, ⟨1, by decide⟩)
private abbrev c11 : Fin (rows diag) × Fin (cols diag) := (⟨1, by decide⟩, ⟨1, by decide⟩)
private abbrev c10 : Fin (rows diag) × Fin (cols diag) := (⟨1, by decide⟩, ⟨0, by decide⟩)

/-- The loop around the four cells of the `2 × 2` grid. -/
private abbrev square : (Grid diag).Walk c00 c00 :=
  .cons (v := c01) (by decide) <| .cons (v := c11) (by decide) <|
    .cons (v := c10) (by decide) <| .cons (by decide) .nil

/-- Two eyes of colour `0` on a diagonal of a `2 × 2` grid: the loop around the grid passes both,
the top left eye sees arms `0, 1, 1, 0` (up, right, down, left) and the bottom right eye sees
`1, 0, 0, 1`, the same view rotated by two quarter turns. -/
example : eyeWitlessDec (bitEncode diag) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, c00, square, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · decide
  · decide

/-- The rotation is needed: the two views above differ as plain lists. -/
example : view diag square (0, 0) = [0, 1, 1, 0] ∧ view diag square (1, 1) = [1, 0, 0, 1] := by
  decide

/-- A grid with fewer than three cells has no loop. -/
private theorem no_cycle {V : Type*} [Finite V] {G : SimpleGraph V} (hV : Nat.card V < 3) {u : V}
    (p : G.Walk u u) : ¬ p.IsCycle := fun h => by
  have := h.three_le_length
  have := h.length_le_natCard
  omega

/-- A single row of two cells, one with an eye, is well formed but has no loop through the eye.
-/
example : eyeWitlessDec (bitEncode ([[1, 0]] : EyeWitlessInstance)) = false := by
  have h : ¬ EyeWitlessFeasible [[1, 0]] := by
    rintro ⟨u, l, hl, -⟩
    exact no_cycle (by simp [rows, cols]) l hl
  simpa [eyeWitlessDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.EyeWitless
