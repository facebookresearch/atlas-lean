/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SuraromuDefs

namespace MetaMathlibExt.Complexity.NPComplete.Suraromu

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SuraromuInstance) :
    suraromuDec (bitEncode i) = true ↔ WellFormed i ∧ SuraromuFeasible i := by
  simp [suraromuDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : suraromuDec [true] = false := by
  have h : bitDecode (α := SuraromuInstance) [true] = none := rfl
  simp [suraromuDec, h]

/-- Adjacency in the grid graph, as a decidable condition on coordinates. -/
private theorem grid_adj (i : SuraromuInstance) (u v : Fin (rows i) × Fin (cols i)) :
    (Grid i).Adj u v ↔
      (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)) ∨
        (u.2 = v.2 ∧ ((u.1 : ℕ) + 1 = v.1 ∨ (v.1 : ℕ) + 1 = u.1)) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
  tauto

/-- A `3 × 3` board with a black center, the circle at `(0, 0)` with number `1`, and one
horizontal gate of length `1` at `(1, 0)` (closed off by the left edge and the black center),
carrying the order number `k`. -/
private abbrev ring (k : ℕ) : SuraromuInstance :=
  ([[false, false, false], [false, true, false], [false, false, false]], (0, 0, 1),
    [(1, 0, 1, false, k)])

/-- A cell of the `3 × 3` board. -/
private def pt (k r c : ℕ) (hr : r < 3 := by decide) (hc : c < 3 := by decide) :
    Fin (rows (ring k)) × Fin (cols (ring k)) :=
  (⟨r, hr⟩, ⟨c, hc⟩)

/-- The loop around the black center, clockwise from the circle cell. -/
private def loop (k : ℕ) : (Grid (ring k)).Walk (pt k 0 0) (pt k 0 0) :=
  .cons (v := pt k 0 1) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 0 2) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 1 2) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 2 2) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 2 1) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 2 0) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 1 0) (by rw [grid_adj]; simp [pt]) <|
  .cons (v := pt k 0 0) (by rw [grid_adj]; simp [pt]) .nil

private theorem wellFormed_ring : WellFormed (ring 1) := by
  unfold WellFormed IsBlack
  decide

/-- The loop around the center crosses the gate once, as its first gate, matching the order
number `1`. -/
example : suraromuDec (bitEncode (ring 1)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_ring, pt 1 0 0, rfl, loop 1, ?_, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  · unfold IsBlack
    decide
  · decide
  · refine ⟨crossings (ring 1) (loop 1), by simp, ?_⟩
    decide

/-- With only one gate, every admissible loop crosses gates exactly once in total, so no gate
can be the second one crossed: the order number `2` makes the instance unsolvable. -/
example : suraromuDec (bitEncode (ring 2)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, u, -, c, -, -, hcount, L, hL, horder⟩ := (accepts_encoding _).1 h
  have hall : ∀ b ∈ crossings (ring 2) c, 0 = b := by
    intro b hb
    simp only [crossings, List.mem_flatMap, gatesAt, List.mem_filter, List.mem_range] at hb
    obtain ⟨-, -, hb, -⟩ := hb
    have : b < 1 := hb
    omega
  have hlen : (crossings (ring 2) c).length = 1 :=
    (List.count_eq_length.2 hall).symm.trans (hcount 0 (by decide))
  have hLlen : L.length = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · exact hlen
    · simpa using hlen
  have h1 : L[1]? = some 0 := horder 0 (by decide) (by decide)
  rw [List.getElem?_eq_none (by omega)] at h1
  exact absurd h1 (by simp)

/-- A circle number different from the number of gates makes the instance malformed. -/
example : suraromuDec (bitEncode
    (([[false, false, false], [false, true, false], [false, false, false]], (0, 0, 2),
      [(1, 0, 1, false, 1)]) : SuraromuInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2.2.2.2.2.2.1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.Suraromu
