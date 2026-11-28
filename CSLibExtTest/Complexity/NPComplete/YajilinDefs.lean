/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.YajilinDefs

namespace MetaMathlibExt.Complexity.NPComplete.Yajilin

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : YajilinInstance) :
    yajilinDec (bitEncode i) = true ↔ WellFormed i ∧ YajilinFeasible i := by
  simp [yajilinDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : yajilinDec [true] = false := by
  have h : bitDecode (α := YajilinInstance) [true] = none := rfl
  simp [yajilinDec, h]

/-- A two-by-three grid whose top-left cell is a clue: `k` shaded cells below it. -/
private abbrev board (k : ℕ) : YajilinInstance :=
  [[(1, k, 1), (0, 0, 0), (0, 0, 0)], [(0, 0, 0), (0, 0, 0), (0, 0, 0)]]

/-- The cell in row `r` and column `c`. -/
private abbrev pt (k r c : ℕ) (hr : r < 2 := by decide) (hc : c < 3 := by decide) : Cell (board k) :=
  (⟨r, hr⟩, ⟨c, hc⟩)

private theorem adj (k r c r' c' : ℕ) (hr : r < 2) (hc : c < 3) (hr' : r' < 2) (hc' : c' < 3)
    (h : (r + 1 = r' ∨ r' + 1 = r) ∧ c = c' ∨ (c + 1 = c' ∨ c' + 1 = c) ∧ r = r') :
    (Grid (board k)).Adj (pt k r c hr hc) (pt k r' c' hr' hc') := by
  simpa [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff] using h

/-- The loop around the right two-by-two block. -/
private def loop (k : ℕ) : (Grid (board k)).Walk (pt k 0 1) (pt k 0 1) :=
  .cons (adj k 0 1 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (.cons (adj k 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (.cons (adj k 1 2 1 1 (by decide) (by decide) (by decide) (by decide) (by decide))
        (.cons (adj k 1 1 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
          .nil)))

/-- Clue "one shaded cell below": the loop around the right block leaves exactly the cell below
the clue shaded, and that cell touches no other shaded cell. -/
example : yajilinDec (bitEncode (board 1)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, _, loop 1, ?_, ?_, ?_, ?_⟩
  · rw [loop, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · decide
  · have hsh : ∀ y, IsShaded (board 1) (loop 1) y → y = pt 1 1 0 := by decide
    rintro x y hxy ⟨hx, hy⟩
    rw [hsh x hx, hsh y hy] at hxy
    exact SimpleGraph.irrefl _ hxy
  · decide

/-- Clue "two shaded cells below" is rejected: only one cell lies below the clue. -/
example : yajilinDec (bitEncode (board 2)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, u, c, -, -, -, hclue⟩
  have h := hclue (pt 2 0 0) (by decide)
  have hsub : (Finset.univ.filter fun y => InDirection (cell (board 2) (pt 2 0 0)).2.2 (pt 2 0 0) y ∧
      IsShaded (board 2) c y) ⊆ Finset.univ.filter fun y =>
        InDirection (cell (board 2) (pt 2 0 0)).2.2 (pt 2 0 0) y :=
    fun y hy => by
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.1⟩
  have hone : (Finset.univ.filter fun y =>
      InDirection (cell (board 2) (pt 2 0 0)).2.2 (pt 2 0 0) y).card = 1 := by
    decide
  have := Finset.card_le_card hsub
  rw [show (cell (board 2) (pt 2 0 0)).2.1 = 2 from rfl] at h
  omega

/-- The rejected instance is well formed, so the rejection comes from the clue. -/
example : WellFormed (board 2) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.Yajilin
