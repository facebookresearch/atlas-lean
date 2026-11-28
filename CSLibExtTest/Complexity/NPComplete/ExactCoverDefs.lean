/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExactCoverDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExactCover

/-- Four overlapping subsets of `{0, 1, 2, 3}`. -/
private abbrev four : ExactCoverInstance := (4, [[0, 1], [1, 2], [2, 3], [3]])

/-- Two overlapping subsets of `{0, 1, 2}`. -/
private abbrev overlap : ExactCoverInstance := (3, [[0, 1], [1, 2]])

private theorem four_wellFormed : WellFormed four := by unfold WellFormed; decide

private theorem overlap_wellFormed : WellFormed overlap := by unfold WellFormed; decide

/-- `[0, 1]` and `[2, 3]` cover each element exactly once. -/
private theorem four_feasible : ExactCoverFeasible four := by
  refine ⟨[[0, 1], [2, 3]], by decide, ?_⟩
  intro x (hx : x < 4)
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl
  · exact ⟨[0, 1], by simp, by rintro y ⟨hy, hx⟩; simp at hy; rcases hy with rfl | rfl <;> simp_all⟩
  · exact ⟨[0, 1], by simp, by rintro y ⟨hy, hx⟩; simp at hy; rcases hy with rfl | rfl <;> simp_all⟩
  · exact ⟨[2, 3], by simp, by rintro y ⟨hy, hx⟩; simp at hy; rcases hy with rfl | rfl <;> simp_all⟩
  · exact ⟨[2, 3], by simp, by rintro y ⟨hy, hx⟩; simp at hy; rcases hy with rfl | rfl <;> simp_all⟩

/-- Covering by all subsets is not exact: `1` lies in two chosen subsets. -/
example : ¬ ∀ x < 4, ∃! s ∈ ([[0, 1], [1, 2], [2, 3], [3]] : List (List ℕ)), x ∈ s := by
  intro h
  obtain ⟨s, -, huniq⟩ := h 1 (by decide)
  have a := huniq [0, 1] ⟨by simp, by simp⟩
  have b := huniq [1, 2] ⟨by simp, by simp⟩
  exact absurd (a.trans b.symm) (by decide)

/-- Covering `0` forces `[0, 1]` and covering `2` forces `[1, 2]`, which then both hold `1`. -/
private theorem overlap_infeasible : ¬ ExactCoverFeasible overlap := by
  rintro ⟨sub, hsub, h⟩
  have pick : ∀ x < 3, ∃ s ∈ sub, x ∈ s := fun x hx => by
    obtain ⟨s, ⟨hs, hx⟩, -⟩ := h x hx
    exact ⟨s, hs, hx⟩
  obtain ⟨s0, hs0, h0⟩ := pick 0 (by decide)
  obtain ⟨s2, hs2, h2⟩ := pick 2 (by decide)
  have m0 : s0 ∈ [[0, 1], [1, 2]] := hsub.subset hs0
  have m2 : s2 ∈ [[0, 1], [1, 2]] := hsub.subset hs2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m0 m2
  obtain rfl : s0 = [0, 1] := by rcases m0 with rfl | rfl <;> simp_all
  obtain rfl : s2 = [1, 2] := by rcases m2 with rfl | rfl <;> simp_all
  obtain ⟨s, -, huniq⟩ := h 1 (by decide)
  have a := huniq [0, 1] ⟨hs0, by simp⟩
  have b := huniq [1, 2] ⟨hs2, by simp⟩
  exact absurd (a.trans b.symm) (by decide)

/-- The empty universe is covered exactly by choosing nothing. -/
private theorem empty_feasible : ExactCoverFeasible ((0, []) : ExactCoverInstance) :=
  ⟨[], by decide, by intro x hx; omega⟩

/-- A non-empty universe with no subsets has no exact cover. -/
example : ¬ ExactCoverFeasible ((1, []) : ExactCoverInstance) := by
  rintro ⟨sub, hsub, h⟩
  obtain ⟨s, ⟨hs, -⟩, -⟩ := h 0 (by decide)
  simp [List.sublist_nil.mp hsub] at hs

/-- A subset with a repeated entry is malformed, although it covers `{0}` exactly once. -/
private theorem repeated_feasible : ExactCoverFeasible ((1, [[0, 0]]) : ExactCoverInstance) := by
  refine ⟨[[0, 0]], by decide, ?_⟩
  intro x hx
  obtain rfl : x = 0 := by omega
  exact ⟨[0, 0], by simp, by rintro y ⟨hy, -⟩; simpa using hy⟩

private theorem repeated_malformed : ¬ WellFormed ((1, [[0, 0]]) : ExactCoverInstance) := by
  unfold WellFormed; decide

/-- A subset with an entry outside the universe is malformed, although it covers `{0}`. -/
private theorem outOfRange_feasible : ExactCoverFeasible ((1, [[0, 1]]) : ExactCoverInstance) := by
  refine ⟨[[0, 1]], by decide, ?_⟩
  intro x hx
  obtain rfl : x = 0 := by omega
  exact ⟨[0, 1], by simp, by rintro y ⟨hy, -⟩; simpa using hy⟩

private theorem outOfRange_malformed : ¬ WellFormed ((1, [[0, 1]]) : ExactCoverInstance) := by
  unfold WellFormed; decide

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the four-subset instance. -/
example : exactCoverDec (bitEncode four) = true := by
  simp [exactCoverDec, four_wellFormed, four_feasible]

/-- It rejects the well-formed overlapping instance. -/
example : exactCoverDec (bitEncode overlap) = false := by
  simp [exactCoverDec, overlap_infeasible]

/-- It accepts the empty universe. -/
example : exactCoverDec (bitEncode ((0, []) : ExactCoverInstance)) = true := by
  have hw : WellFormed ((0, []) : ExactCoverInstance) := by unfold WellFormed; decide
  simp [exactCoverDec, hw, empty_feasible]

/-- It rejects feasible malformed instances. -/
example :
    exactCoverDec (bitEncode ((1, [[0, 0]]) : ExactCoverInstance)) = false ∧
      exactCoverDec (bitEncode ((1, [[0, 1]]) : ExactCoverInstance)) = false := by
  simp [exactCoverDec, repeated_malformed, outOfRange_malformed]

example :
    ExactCoverFeasible ((1, [[0, 0]]) : ExactCoverInstance) ∧
      ExactCoverFeasible ((1, [[0, 1]]) : ExactCoverInstance) :=
  ⟨repeated_feasible, outOfRange_feasible⟩

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : exactCoverDec [] = false := by
  have h : bitDecode (α := ExactCoverInstance) [] = none := rfl
  simp [exactCoverDec, h]

end MetaMathlibExt.Complexity.NPComplete.ExactCover
