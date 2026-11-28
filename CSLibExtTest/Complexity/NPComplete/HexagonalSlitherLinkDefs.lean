/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HexagonalSlitherLinkDefs

namespace MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HexagonalSlitherLinkInstance) :
    hexagonalSlitherLinkDec (bitEncode i) = true ↔
      WellFormed i ∧ HexagonalSlitherLinkFeasible i := by
  simp [hexagonalSlitherLinkDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hexagonalSlitherLinkDec [true] = false := by
  have h : bitDecode (α := HexagonalSlitherLinkInstance) [true] = none := rfl
  simp [hexagonalSlitherLinkDec, h]

/-- The loop around the six corners of the single hexagon `(0, 0)`, clockwise from the top
left corner. -/
private abbrev loop : (Graph [[7]]).Walk (0, 0) (0, 0) :=
  .cons (v := (1, 0)) (by unfold Graph; decide) <|
    .cons (v := (1, 1)) (by unfold Graph; decide) <|
      .cons (v := (1, 2)) (by unfold Graph; decide) <|
        .cons (v := (0, 2)) (by unfold Graph; decide) <|
          .cons (v := (0, 1)) (by unfold Graph; decide) <|
            .cons (by unfold Graph; decide) .nil

/-- A single hexagon with clue `6` (entry `7`): the loop around it uses all six sides. -/
example : hexagonalSlitherLinkDec (bitEncode ([[7]] : HexagonalSlitherLinkInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, (0, 0), loop, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · decide

/-- A single hexagon with clue `0` (entry `1`) is well formed, but every edge of the grid is a
side of that hexagon, so every loop uses at least one of its sides. -/
example : hexagonalSlitherLinkDec (bitEncode ([[1]] : HexagonalSlitherLinkInstance)) = false := by
  have h : ¬ HexagonalSlitherLinkFeasible [[1]] := by
    rintro ⟨u, cyc, hcyc, hclue⟩
    have hzero := hclue 0 (by decide) 0 (by decide) (by decide)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil cyc.edges
      (by simpa [SimpleGraph.Walk.edges_eq_nil] using hcyc.ne_nil)
    have hside : e ∈ sides 0 0 := by
      induction e using Sym2.ind with
      | _ p q =>
        obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).1 (cyc.adj_of_mem_edges he)
        rcases hr with ⟨c, hc, r, hr, hs⟩ | ⟨c, hc, r, hr, hs⟩
        · obtain rfl : c = 0 := by simpa [width] using hc
          obtain rfl : r = 0 := by simpa [height] using hr
          exact hs
        · obtain rfl : c = 0 := by simpa [width] using hc
          obtain rfl : r = 0 := by simpa [height] using hr
          rwa [Sym2.eq_swap]
    have : 0 < (sides 0 0).countP (· ∈ cyc.edges) := List.countP_pos_iff.2 ⟨e, hside, by simpa⟩
    have : clue [[1]] 0 0 = 1 := rfl
    omega
  simpa [hexagonalSlitherLinkDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink
