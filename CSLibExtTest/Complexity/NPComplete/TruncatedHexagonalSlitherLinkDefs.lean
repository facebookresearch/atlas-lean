/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module


import CSLibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLinkDefs

namespace MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TruncatedHexagonalSlitherLinkInstance) :
    truncatedHexagonalSlitherLinkDec (bitEncode i) = true ↔
      WellFormed i ∧ TruncatedHexagonalSlitherLinkFeasible i := by
  simp [truncatedHexagonalSlitherLinkDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : truncatedHexagonalSlitherLinkDec [true] = false := by
  have h : bitDecode (α := TruncatedHexagonalSlitherLinkInstance) [true] = none := rfl
  simp [truncatedHexagonalSlitherLinkDec, h]

/-- One row of two dodecagons with the given dodecagon clue entries and no triangle clues. -/
private abbrev twoCells (a b : ℕ) : TruncatedHexagonalSlitherLinkInstance :=
  ([[a, b]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]])

/-- No triangle of an instance of this shape carries a clue. -/
private theorem twoCells_noTriangleClue (a b : ℕ) :
    ∀ y ≤ height (twoCells a b), ∀ x ≤ 2 * width (twoCells a b) + 1,
      ¬ 0 < triangleClue (twoCells a b) x y := by
  simp only [height, width, triangleClue, List.length_cons, List.length_nil,
    List.headD_cons]
  decide

/-- Any instance of this shape is well formed: it has no triangle clues. -/
private theorem twoCells_wellFormed (a b : ℕ) : WellFormed (twoCells a b) := by
  refine ⟨by simp [height], by simp [width], by simp [width], rfl, by simp [width], ?_⟩
  intro y hy x hx hpos
  exact absurd hpos (twoCells_noTriangleClue a b y hy x hx)

/-- Two ends of a side of the first dodecagon are adjacent. -/
private theorem adj (u v : Point) (h : u ≠ v ∧ s(u, v) ∈ dodecagonSides 0 0) :
    (Graph (twoCells 13 0)).Adj u v := by
  simp only [Graph, SimpleGraph.fromRel_adj]
  exact ⟨h.1, Or.inl ⟨0, by simp [width], 0, by simp [height], h.2⟩⟩

/-- The boundary of the first dodecagon, through its twelve vertices. -/
private def boundary : (Graph (twoCells 13 0)).Walk ((0, 0), (0, 1)) ((0, 0), (0, 1)) :=
  .cons (adj ((0, 0), (0, 1)) ((0, 0), (1, 0)) (by decide))
      (.cons (adj ((0, 0), (1, 0)) ((1, 0), (0, 0)) (by decide))
      (.cons (adj ((1, 0), (0, 0)) ((1, 0), (2, 0)) (by decide))
      (.cons (adj ((1, 0), (2, 0)) ((2, 0), (1, 0)) (by decide))
      (.cons (adj ((2, 0), (1, 0)) ((2, 0), (2, 1)) (by decide))
      (.cons (adj ((2, 0), (2, 1)) ((2, 1), (2, 0)) (by decide))
      (.cons (adj ((2, 1), (2, 0)) ((2, 1), (1, 1)) (by decide))
      (.cons (adj ((2, 1), (1, 1)) ((1, 1), (2, 1)) (by decide))
      (.cons (adj ((1, 1), (2, 1)) ((1, 1), (0, 1)) (by decide))
      (.cons (adj ((1, 1), (0, 1)) ((0, 1), (1, 1)) (by decide))
      (.cons (adj ((0, 1), (1, 1)) ((0, 1), (0, 0)) (by decide))
      (.cons (adj ((0, 1), (0, 0)) ((0, 0), (0, 1)) (by decide)) .nil)))))))))))

/-- Clue `12` on the first dodecagon is met by its own boundary. -/
example : truncatedHexagonalSlitherLinkDec (bitEncode (twoCells 13 0)) = true := by
  apply (accepts_encoding _).2
  refine ⟨twoCells_wellFormed 13 0, _, boundary, ?_, ?_, ?_⟩
  · rw [boundary, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · unfold height width dodecagonClue
    decide
  · intro y hy x hx hpos
    exact absurd hpos (twoCells_noTriangleClue 13 0 y hy x hx)

/-- Clue `0` on the first dodecagon and clue `12` on the second contradict each other: the
side they share must be both absent and present. -/
example : truncatedHexagonalSlitherLinkDec (bitEncode (twoCells 1 13)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, u, cyc, -, hclue, -⟩
  have h0 := hclue 0 (by decide) 0 (by decide) (by decide)
  have h1 := hclue 0 (by decide) 1 (by decide) (by decide)
  simp only [dodecagonClue] at h0 h1
  have hout : ∀ e ∈ dodecagonSides 0 0, e ∉ cyc.edges := by simpa using h0
  have h1' : (dodecagonSides 1 0).countP (· ∈ cyc.edges) = (dodecagonSides 1 0).length := by
    rw [show (dodecagonSides 1 0).length = 12 from rfl]
    simpa using h1
  have hin := List.countP_eq_length.1 h1' s(((2, 1), (2, 0)), ((2, 0), (2, 1))) (by decide)
  rw [Sym2.eq_swap] at hin
  exact hout s(((2, 0), (2, 1)), ((2, 1), (2, 0))) (by decide) (by simpa using hin)

/-- The rejected instance is well formed, so the rejection comes from the clues. -/
example : WellFormed (twoCells 1 13) := twoCells_wellFormed 1 13

end MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink
