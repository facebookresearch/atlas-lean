/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaxCutDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaxCut

/-- The triangle on the vertices `0`, `1`, `2` with the bound `K`. -/
private abbrev triangle (K : ℕ) : MaxCutInstance :=
  (3, [(0, 1), (1, 2), (0, 2)], K)

/-- The triangle is well formed. -/
example : WellFormed (triangle 2) := by unfold WellFormed; decide

/-- The side `{0}` cuts the two edges at `0`, which form a sublist of the edges in their order,
so the triangle has a cut of size `2`. -/
private theorem triangle_two_feasible : MaxCutFeasible (triangle 2) :=
  ⟨{0}, by decide, [(0, 1), (0, 2)], by decide, by decide, by decide⟩

/-- No cut of the triangle has size `3`: such a cut would hold all three edges, and an odd
cycle cannot have every edge cross between the two sides. The bound equals the number of
edges, so only the crossing condition rules it out. -/
private theorem triangle_three_infeasible : ¬ MaxCutFeasible (triangle 3) := by
  rintro ⟨S, -, cut, hsub, hlen, hcross⟩
  obtain rfl : cut = [(0, 1), (1, 2), (0, 2)] := hsub.eq_of_length_le (by simpa using hlen)
  have a := hcross (0, 1) (by simp)
  have b := hcross (1, 2) (by simp)
  have c := hcross (0, 2) (by simp)
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S <;> by_cases h2 : 2 ∈ S <;> simp_all

/-- The cut must be a sublist: the two edges at `0` in the other order are not one. -/
example : ¬ [((0 : ℕ), (2 : ℕ)), (0, 1)].Sublist [(0, 1), (1, 2), (0, 2)] := by decide

/-- A cut cannot repeat an edge: the single edge of a path on two vertices gives no cut of
size `2`, although that edge crosses between `{0}` and `{1}`. -/
example : ¬ MaxCutFeasible (2, [(0, 1)], 2) := by
  rintro ⟨S, -, cut, hsub, hlen, -⟩
  have h := hsub.length_le
  change cut.length ≤ 1 at h
  change 2 ≤ cut.length at hlen
  omega

/-- The bound `0` is met by the empty side and the empty cut. -/
example : MaxCutFeasible (triangle 0) := ⟨∅, by decide, [], by decide, by decide, by decide⟩

/-- The empty graph is well formed, and meets the bound `0`. -/
private theorem empty_wellFormed : WellFormed ((0, [], 0) : MaxCutInstance) := by
  unfold WellFormed; decide

private theorem empty_feasible : MaxCutFeasible ((0, [], 0) : MaxCutInstance) :=
  ⟨∅, by decide, [], by decide, by decide, by decide⟩

/-- The empty graph has no cut of size `1`. -/
example : ¬ MaxCutFeasible ((0, [], 1) : MaxCutInstance) := by
  rintro ⟨S, -, cut, hsub, hlen, -⟩
  have h := hsub.length_le
  change cut.length ≤ 0 at h
  change 1 ≤ cut.length at hlen
  omega

/-- The side may only hold vertices: every edge of `(2, [(5, 6)], 1)` lies outside the two
vertices `0` and `1`, so no side of them cuts it, although the side `{5}` would. -/
example : ¬ MaxCutFeasible ((2, [(5, 6)], 1) : MaxCutInstance) := by
  rintro ⟨S, hS, cut, hsub, hlen, hcross⟩
  obtain rfl : cut = [(5, 6)] := hsub.eq_of_length_le (by simpa using hlen)
  rcases hcross (5, 6) (by simp) with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (hS 5 h) (by decide)
  · exact absurd (hS 6 h) (by decide)

/-- A repeated edge is malformed, although both copies cross between `{0}` and `{1}`. -/
private theorem duplicate_feasible : MaxCutFeasible ((2, [(0, 1), (0, 1)], 2) : MaxCutInstance) :=
  ⟨{0}, by decide, [(0, 1), (0, 1)], by decide, by decide, by decide⟩

private theorem duplicate_malformed : ¬ WellFormed ((2, [(0, 1), (0, 1)], 2) : MaxCutInstance) := by
  unfold WellFormed; decide

/-- An edge listed in both directions is malformed, although both entries cross. -/
private theorem reversed_feasible : MaxCutFeasible ((2, [(0, 1), (1, 0)], 2) : MaxCutInstance) :=
  ⟨{0}, by decide, [(0, 1), (1, 0)], by decide, by decide, by decide⟩

private theorem reversed_malformed : ¬ WellFormed ((2, [(0, 1), (1, 0)], 2) : MaxCutInstance) := by
  unfold WellFormed; decide

/-- A loop is malformed; it never crosses, but the bound `0` is still met. -/
private theorem loop_feasible : MaxCutFeasible ((1, [(0, 0)], 0) : MaxCutInstance) :=
  ⟨∅, by decide, [], by decide, by decide, by decide⟩

private theorem loop_malformed : ¬ WellFormed ((1, [(0, 0)], 0) : MaxCutInstance) := by
  unfold WellFormed; decide

/-- An endpoint outside the vertices is malformed, although the side `{0}` cuts the edge. -/
private theorem outOfRange_feasible : MaxCutFeasible ((2, [(0, 5)], 1) : MaxCutInstance) :=
  ⟨{0}, by decide, [(0, 5)], by decide, by decide, by decide⟩

private theorem outOfRange_malformed : ¬ WellFormed ((2, [(0, 5)], 1) : MaxCutInstance) := by
  unfold WellFormed; decide

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the encoding of the triangle with the bound `2`. -/
example : maxCutDec (bitEncode (triangle 2)) = true := by
  have hw : WellFormed (triangle 2) := by unfold WellFormed; decide
  simp [maxCutDec, hw, triangle_two_feasible]

/-- It rejects the encoding of the well-formed triangle with the bound `3`. -/
example : maxCutDec (bitEncode (triangle 3)) = false := by
  simp [maxCutDec, triangle_three_infeasible]

/-- It accepts the encoding of the empty graph with the bound `0`. -/
example : maxCutDec (bitEncode ((0, [], 0) : MaxCutInstance)) = true := by
  simp [maxCutDec, empty_wellFormed, empty_feasible]

/-- It rejects the encodings of malformed instances that have a cut of the requested size:
a repeated edge, an edge in both directions, a loop and an endpoint outside the vertices. -/
example :
    maxCutDec (bitEncode ((2, [(0, 1), (0, 1)], 2) : MaxCutInstance)) = false ∧
      maxCutDec (bitEncode ((2, [(0, 1), (1, 0)], 2) : MaxCutInstance)) = false ∧
      maxCutDec (bitEncode ((1, [(0, 0)], 0) : MaxCutInstance)) = false ∧
      maxCutDec (bitEncode ((2, [(0, 5)], 1) : MaxCutInstance)) = false := by
  simp [maxCutDec, duplicate_malformed, reversed_malformed, loop_malformed,
    outOfRange_malformed]

/-- Those instances are feasible, so `WellFormed` alone rejects them. -/
example :
    MaxCutFeasible ((2, [(0, 1), (0, 1)], 2) : MaxCutInstance) ∧
      MaxCutFeasible ((2, [(0, 1), (1, 0)], 2) : MaxCutInstance) ∧
      MaxCutFeasible ((1, [(0, 0)], 0) : MaxCutInstance) ∧
      MaxCutFeasible ((2, [(0, 5)], 1) : MaxCutInstance) :=
  ⟨duplicate_feasible, reversed_feasible, loop_feasible, outOfRange_feasible⟩

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : maxCutDec [] = false := by
  have h : bitDecode (α := MaxCutInstance) [] = none := rfl
  simp [maxCutDec, h]

end MetaMathlibExt.Complexity.NPComplete.MaxCut
