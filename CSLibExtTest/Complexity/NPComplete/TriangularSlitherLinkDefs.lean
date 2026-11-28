/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TriangularSlitherLinkDefs

namespace MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TriangularSlitherLinkInstance) :
    triangularSlitherLinkDec (bitEncode i) = true ↔
      WellFormed i ∧ TriangularSlitherLinkFeasible i := by
  simp [triangularSlitherLinkDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : triangularSlitherLinkDec [true] = false := by
  have h : bitDecode (α := TriangularSlitherLinkInstance) [true] = none := rfl
  simp [triangularSlitherLinkDec, h]

/-- Two rows of two triangles, with clue `3` on the first (down) triangle. -/
private abbrev clue3 : TriangularSlitherLinkInstance := [[4, 0], [0, 0]]

private theorem adj₁ : (Graph clue3).Adj (0, 0) (1, 0) := by
  simp [Graph, GridEdge, width, height]

private theorem adj₂ : (Graph clue3).Adj (1, 0) (0, 1) := by
  simp [Graph, GridEdge, width, height]

private theorem adj₃ : (Graph clue3).Adj (0, 1) (0, 0) := by
  simp [Graph, GridEdge, width, height]

/-- The boundary of the clue triangle is a cycle using all three of its sides. -/
example : triangularSlitherLinkDec (bitEncode clue3) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed width height; decide, (0, 0),
    .cons adj₁ (.cons adj₂ (.cons adj₃ .nil)), ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · unfold height width clue sides corners
    decide

/-- Clue `0` on the first triangle and clue `3` on its up-neighbour contradict each other:
the side they share must be both absent and present. -/
example : triangularSlitherLinkDec (bitEncode [[1, 4], [0, 0]]) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, u, c, -, hclue⟩
  have h0 := hclue 0 (by decide) 0 (by decide) (by decide)
  have h1 := hclue 0 (by decide) 1 (by decide) (by decide)
  simp only [clue] at h0 h1
  have hout : ∀ e ∈ sides 0 0, e ∉ c.edges := by simpa using h0
  have h1' : (sides 0 1).countP (· ∈ c.edges) = (sides 0 1).length := by
    rw [show (sides 0 1).length = 3 from rfl]
    simpa using h1
  have hin := List.countP_eq_length.1 h1' (s((0, 1), (1, 0))) (by decide)
  rw [Sym2.eq_swap] at hin
  exact hout s((1, 0), (0, 1)) (by decide) (by simpa using hin)

/-- The rejected instance is well formed, so the rejection comes from the clues. -/
example : WellFormed ([[1, 4], [0, 0]] : TriangularSlitherLinkInstance) := by
  unfold WellFormed width height
  decide

end MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink
