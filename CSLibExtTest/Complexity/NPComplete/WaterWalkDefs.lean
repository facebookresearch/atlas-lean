/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WaterWalkDefs

namespace MetaMathlibExt.Complexity.NPComplete.WaterWalk

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : WaterWalkInstance) :
    waterWalkDec (bitEncode i) = true ↔ WellFormed i ∧ WaterWalkFeasible i := by
  simp [waterWalkDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : waterWalkDec [true] = false := by
  have h : bitDecode (α := WaterWalkInstance) [true] = none := rfl
  simp [waterWalkDec, h]

/-- A two-by-two all-ground grid with number `k` in the top-left cell. -/
private abbrev block (k : ℕ) : WaterWalkInstance := [[(false, k), (false, 0)], [(false, 0), (false, 0)]]

/-- The cell in row `r` and column `c` of the block. -/
private abbrev pt (k r c : ℕ) (hr : r < 2 := by decide) (hc : c < 2 := by decide) :
    Fin (rows (block k)) × Fin (cols (block k)) :=
  (⟨r, by simpa [rows] using hr⟩, ⟨c, by simpa [cols] using hc⟩)

private theorem adj (k r c r' c' : ℕ) (hr : r < 2) (hc : c < 2) (hr' : r' < 2) (hc' : c' < 2)
    (h : (r + 1 = r' ∨ r' + 1 = r) ∧ c = c' ∨ (c + 1 = c' ∨ c' + 1 = c) ∧ r = r') :
    (Grid (block k)).Adj (pt k r c hr hc) (pt k r' c' hr' hc') := by
  simpa [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff] using h

/-- The loop around the four cells of the block. -/
private def loop (k : ℕ) : (Grid (block k)).Walk (pt k 0 0) (pt k 0 0) :=
  .cons (adj k 0 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
    (.cons (adj k 0 1 1 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (.cons (adj k 1 1 1 0 (by decide) (by decide) (by decide) (by decide) (by decide))
        (.cons (adj k 1 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide))
          .nil)))

/-- The loop around the block passes four ground cells, matching the number `4`. -/
example : waterWalkDec (bitEncode (block 4)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed rows cols; decide, _, loop 4, ?_, ?_⟩
  · rw [loop, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · refine ⟨?_, ?_, ?_⟩
    · decide
    · decide
    · decide

/-- Number `5` cannot be met: every cycle of the block has at most four cells, and with no
water the numbered cell's section is the whole loop. -/
example : waterWalkDec (bitEncode (block 5)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, u, c, hc, h₁, h₂, -⟩
  have hground : ∀ x, (cell (block 5) x).1 = false := by
    unfold cell
    decide
  have hlen : c.length ≤ 4 := by
    have h₃ := hc.support_nodup.length_le_card
    have h₄ : Fintype.card (Fin (rows (block 5)) × Fin (cols (block 5))) = 4 := by
      simp [rows, cols]
    have h₅ := SimpleGraph.Walk.length_support c
    have h₆ := List.length_tail (l := c.support)
    omega
  obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 (h₁ (pt 5 0 0)
    (by simp [cell]))
  have hpos : 0 < c.length := hc.three_le_length.trans_lt' (by decide)
  have hj : ∃ j < c.length, c.getVert j = pt 5 0 0 := by
    rcases hnle.lt_or_eq with hlt | rfl
    · exact ⟨n, hlt, hn⟩
    · exact ⟨0, hpos, by rw [SimpleGraph.Walk.getVert_zero, ← hn,
        SimpleGraph.Walk.getVert_length]⟩
  obtain ⟨j, hjlt, hjv⟩ := hj
  have hnum : (cell (block 5) (c.getVert j)).2 = 5 := by rw [hjv]; simp [cell]
  rcases h₂ j hjlt (by omega) with ⟨-, hk⟩ | ⟨a, -, -, hwater, -⟩
  · omega
  · simp [hground] at hwater

/-- The rejected instance is well formed, so the rejection comes from the number. -/
example : WellFormed (block 5) := by
  unfold WellFormed rows cols
  decide

end MetaMathlibExt.Complexity.NPComplete.WaterWalk
