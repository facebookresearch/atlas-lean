/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SlitherLinkDefs

namespace MetaMathlibExt.Complexity.NPComplete.SlitherLink

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SlitherLinkInstance) :
    slitherLinkDec (bitEncode i) = true ↔ WellFormed i ∧ SlitherLinkFeasible i := by
  simp [slitherLinkDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : slitherLinkDec [true] = false := by
  have h : bitDecode (α := SlitherLinkInstance) [true] = none := rfl
  simp [slitherLinkDec, h]

/-- Adjacency in the lattice graph, as a decidable condition on coordinates. -/
private theorem lattice_adj (i : SlitherLinkInstance) (u v : Point i) : (Lattice i).Adj u v ↔
    (u.2 = v.2 ∧ ((u.1 : ℕ) + 1 = v.1 ∨ (v.1 : ℕ) + 1 = u.1)) ∨
      (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
  tauto

/-- Two cells side by side, each carrying the number `3`. -/
private abbrev twoThrees : SlitherLinkInstance := [[4, 4]]

/-- The boundary of the two cells, `(0,0) → (0,1) → (0,2) → (1,2) → (1,1) → (1,0) → (0,0)`. -/
private def boundary : (Lattice twoThrees).Walk (0, 0) (0, 0) :=
  .cons (u := (0, 0)) (v := (0, 1)) (by rw [lattice_adj]; decide) <|
  .cons (v := (0, 2)) (by rw [lattice_adj]; decide) <|
  .cons (v := (1, 2)) (by rw [lattice_adj]; decide) <|
  .cons (v := (1, 1)) (by rw [lattice_adj]; decide) <|
  .cons (v := (1, 0)) (by rw [lattice_adj]; decide) <|
  .cons (v := (0, 0)) (by rw [lattice_adj]; decide) .nil

/-- The boundary of two adjacent `3`s uses three sides of each cell. -/
example : slitherLinkDec (bitEncode twoThrees) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, (0, 0), boundary, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  · unfold boundary sides clue
    decide

/-- Every edge of the `2 × 2` lattice is a side of its only cell. -/
private theorem edge_mem_sides (x y : Point [[1]])
    (h : (x.2 = y.2 ∧ ((x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1)) ∨
      (x.1 = y.1 ∧ ((x.2 : ℕ) + 1 = y.2 ∨ (y.2 : ℕ) + 1 = x.2))) :
    s(x, y) ∈ sides [[1]] ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  revert x y
  unfold sides
  decide

/-- A single cell numbered `0`: every edge of the `2 × 2` lattice is a side of that cell, and a
cycle has at least one edge, so the number `0` cannot be met. -/
example : slitherLinkDec (bitEncode ([[1]] : SlitherLinkInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, u, c, hc, hclue⟩ := (accepts_encoding _).1 h
  have hsides : ∀ e ∈ c.edges, e ∈ sides [[1]] ⟨0, by decide⟩ ⟨0, by decide⟩ := by
    intro e he
    have hes := c.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet, lattice_adj] at hes
      exact edge_mem_sides x y hes
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil c.edges (by
    intro hnil
    exact hc.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hnil))
  have hpos : 0 < (sides [[1]] ⟨0, by decide⟩ ⟨0, by decide⟩).countP (· ∈ c.edges) := by
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ sides [[1]] ⟨0, by decide⟩ ⟨0, by decide⟩, s = e :=
      ⟨e, hsides e he, rfl⟩
    exact List.countP_pos_iff.2 ⟨s, hs, by simpa using he⟩
  have := hclue ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
  change (sides [[1]] ⟨0, by decide⟩ ⟨0, by decide⟩).countP (· ∈ c.edges) + 1 = 1 at this
  omega

/-- The number `4` (entry `5`) is outside the allowed range `0`–`3`. -/
example : slitherLinkDec (bitEncode ([[5]] : SlitherLinkInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.2.2 [5] (by simp) 5 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.SlitherLink
