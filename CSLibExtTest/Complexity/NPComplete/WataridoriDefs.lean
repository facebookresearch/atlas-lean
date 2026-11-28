/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WataridoriDefs

namespace MetaMathlibExt.Complexity.NPComplete.Wataridori

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : WataridoriInstance) :
    wataridoriDec (bitEncode i) = true ↔ WellFormed i ∧ WataridoriFeasible i := by
  simp [wataridoriDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : wataridoriDec [true] = false := by
  have h : bitDecode (α := WataridoriInstance) [true] = none := rfl
  simp [wataridoriDec, h]

/-- A one-by-two grid forming a single region, with a circle of mark `m` in both cells. -/
private abbrev twoCircles (m : ℕ) : WataridoriInstance := (1, [[(0, m), (0, m)]])

/-- The left cell. -/
private abbrev left (m : ℕ) : Fin (rows (twoCircles m)) × Fin (cols (twoCircles m)) :=
  (⟨0, by simp [rows]⟩, ⟨0, by simp [cols]⟩)

/-- The right cell. -/
private abbrev right (m : ℕ) : Fin (rows (twoCircles m)) × Fin (cols (twoCircles m)) :=
  (⟨0, by simp [rows]⟩, ⟨1, by simp [cols]⟩)

private theorem cells (m : ℕ) (x : Fin (rows (twoCircles m)) × Fin (cols (twoCircles m))) :
    x = left m ∨ x = right m := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp [rows, cols] at ha hb
  subst ha
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp

private theorem adj (m : ℕ) : (Grid (twoCircles m)).Adj (left m) (right m) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]

/-- Every instance of this shape is well formed: its one region is the whole connected grid. -/
private theorem twoCircles_wellFormed (m : ℕ) : WellFormed (twoCircles m) := by
  refine ⟨by simp [rows], by simp [cols], by simp [cols], by simp, ?_⟩
  intro k hk
  obtain rfl : k = 0 := by simpa using hk
  have hmem : ∀ x, x ∈ {x | (cell (twoCircles m) x).1 = 0} := by
    intro x
    rcases cells m x with rfl | rfl <;> simp [cell]
  have hbase : ∀ u, ((Grid (twoCircles m)).induce {x | (cell (twoCircles m) x).1 = 0}).Reachable
      ⟨left m, hmem _⟩ u := by
    rintro ⟨u, hu⟩
    rcases cells m u with rfl | rfl
    · rfl
    · exact SimpleGraph.Adj.reachable (by simpa using adj m)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => (hbase u).symm.trans (hbase v), ⟨⟨left m, hmem _⟩⟩⟩

/-- Two circles numbered `1` are joined by a path through the single region. -/
example : wataridoriDec (bitEncode (twoCircles 3)) = true := by
  apply (accepts_encoding _).2
  refine ⟨twoCircles_wellFormed 3, [⟨left 3, right 3, .cons (adj 3) .nil⟩], ?_, by decide, ?_⟩
  · simp only [List.mem_singleton]
    rintro p rfl
    unfold PathOK regions
    rw [SimpleGraph.Walk.isPath_def]
    decide
  · intro x _
    rcases cells 3 x with rfl | rfl <;> simp

/-- Two circles numbered `2` are rejected: every path in a one-region grid passes through only
one region. -/
example : wataridoriDec (bitEncode (twoCircles 4)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, ps, hok, -, hcover⟩
  obtain ⟨p, hp, hend⟩ := hcover (left 4) (by simp [cell])
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := hok p hp
  have hlen : (regions (twoCircles 4) p.2.2).length ≤ 1 := by
    have hzero : ∀ a ∈ regions (twoCircles 4) p.2.2, a = 0 := by
      intro a ha
      simp only [regions, List.mem_dedup, List.mem_map] at ha
      obtain ⟨x, -, rfl⟩ := ha
      rcases cells 4 x with rfl | rfl <;> simp [cell]
    have hnd : (regions (twoCircles 4) p.2.2).Nodup := List.nodup_dedup _
    match hr : regions (twoCircles 4) p.2.2, hzero, hnd with
    | [], _, _ => simp
    | [_], _, _ => simp
    | a :: b :: _, hz, hn =>
      simp only [List.nodup_cons, List.mem_cons] at hn
      exact absurd (Or.inl ((hz a (by simp)).trans (hz b (by simp)).symm)) hn.1
  have hmark : (cell (twoCircles 4) (left 4)).2 = 4 := by simp [cell]
  rcases hend with h | h
  · have hm : (cell (twoCircles 4) p.1).2 = 4 := h ▸ hmark
    rw [hm] at h₁
    have := h₁ (by omega)
    omega
  · have hm : (cell (twoCircles 4) p.2.1).2 = 4 := h ▸ hmark
    rw [hm] at h₂
    have := h₂ (by omega)
    omega

/-- The rejected instance is well formed, so the rejection comes from the circle numbers. -/
example : WellFormed (twoCircles 4) := twoCircles_wellFormed 4

end MetaMathlibExt.Complexity.NPComplete.Wataridori
