/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.AkariDefs

namespace MetaMathlibExt.Complexity.NPComplete.Akari

/-- A bulb illuminates its own cell. -/
private theorem illuminates_self (board : List (List ℕ)) (r c : ℕ) :
    Illuminates board r c r c :=
  Or.inl ⟨rfl, fun cc h => by omega⟩

/-- A bulb shines along its row through empty cells. -/
example : Illuminates [[0, 0, 0]] 0 0 0 2 := by
  refine Or.inl ⟨rfl, fun cc h => ?_⟩
  obtain rfl : cc = 1 := by simp at h; omega
  rfl

/-- A bulb shines along its column through empty cells. -/
example : Illuminates [[0], [0], [0]] 2 0 0 0 := by
  refine Or.inr ⟨rfl, fun rr h => ?_⟩
  obtain rfl : rr = 1 := by simp at h; omega
  rfl

/-- A wall stops the light. -/
private theorem wall_blocks (k : ℕ) (hk : k ≠ 0) : ¬ Illuminates [[0, k, 0]] 0 0 0 2 := by
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · exact hk (h 1 (by simp))
  · omega

/-- A bulb does not shine diagonally. -/
example : ¬ Illuminates [[0, 0], [0, 0]] 0 0 1 1 := by
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega

/-- A single empty cell is lit by one bulb on it. -/
private theorem single_feasible : AkariFeasible [[0]] := by
  refine ⟨[(0, 0)], by decide, by decide, ?_, ?_, by decide⟩
  · intro r hr c hc _
    exact ⟨(0, 0), by simp, by simp at hr hc; subst hr; subst hc; exact illuminates_self _ 0 0⟩
  · intro b hb b' hb' hne
    simp at hb hb'
    exact absurd (hb.trans hb'.symm) hne

/-- With no bulbs, a single empty cell is dark. -/
example : ¬ ∃ b ∈ ([] : List (ℕ × ℕ)), Illuminates [[0]] b.1 b.2 0 0 := by
  simp

/-- The bulbs of a row `0, w, 0` with a wall `w` in the middle: the only empty cells are the two
ends, and the wall keeps each end dark unless it carries a bulb. -/
private theorem ends_mem {w : ℕ} (hw : w ≠ 0) {bulbs : List (ℕ × ℕ)}
    (hpos : ∀ p ∈ bulbs, p.1 < [[0, w, 0]].length ∧ p.2 < ([[0, w, 0]].getD 0 []).length ∧
      ([[0, w, 0]].getD p.1 []).getD p.2 1 = 0)
    (hlit : ∀ r < [[0, w, 0]].length, ∀ c < ([[0, w, 0]].getD 0 []).length,
      ([[0, w, 0]].getD r []).getD c 1 = 0 → ∃ b ∈ bulbs, Illuminates [[0, w, 0]] b.1 b.2 r c) :
    (0, 0) ∈ bulbs ∧ (0, 2) ∈ bulbs := by
  have cell : ∀ b ∈ bulbs, b = (0, 0) ∨ b = (0, 2) := by
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hpos b hb
    obtain ⟨r, c⟩ := b
    simp at h1 h2 h3
    subst h1
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp_all
  constructor
  · obtain ⟨b, hb, hill⟩ := hlit 0 (by simp) 0 (by simp) rfl
    rcases cell b hb with rfl | rfl
    · exact hb
    · rcases hill with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd (h 1 (by simp)) (by simpa using hw)
      · simp at h
  · obtain ⟨b, hb, hill⟩ := hlit 0 (by simp) 2 (by simp) rfl
    rcases cell b hb with rfl | rfl
    · rcases hill with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd (h 1 (by simp)) (by simpa using hw)
      · simp at h
    · exact hb

/-- A wall numbered `1` between two empty cells cannot be satisfied: both ends need a bulb, so
the wall has two neighbouring bulbs. -/
private theorem numberedOne_infeasible : ¬ AkariFeasible [[0, 3, 0]] := by
  rintro ⟨bulbs, hnd, hpos, hlit, -, hnum⟩
  obtain ⟨h0, h2⟩ := ends_mem (by decide) hpos hlit
  have hcount := hnum 0 (by simp) 1 (by simp) (by simp)
  have hsub : [((0 : ℕ), (0 : ℕ)), (0, 2)].Subperm (bulbs.filter fun b =>
      (b.1 == 0 + 1 && b.2 == 1) || (b.1 + 1 == 0 && b.2 == 1) ||
        (b.1 == 0 && b.2 == 1 + 1) || (b.1 == 0 && b.2 + 1 == 1)) := by
    refine List.subperm_of_subset (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [List.mem_filter, h0, h2]
  have := hsub.length_le
  simp at hcount this
  omega

/-- A wall numbered `0` between two empty cells cannot be satisfied either. -/
example : ¬ AkariFeasible [[0, 2, 0]] := by
  rintro ⟨bulbs, hnd, hpos, hlit, -, hnum⟩
  obtain ⟨h0, -⟩ := ends_mem (by decide) hpos hlit
  have hcount := hnum 0 (by simp) 1 (by simp) (by simp)
  have : (0, 0) ∈ bulbs.filter fun b =>
      (b.1 == 0 + 1 && b.2 == 1) || (b.1 + 1 == 0 && b.2 == 1) ||
        (b.1 == 0 && b.2 == 1 + 1) || (b.1 == 0 && b.2 + 1 == 1) := by
    simp [List.mem_filter, h0]
  have := List.length_pos_of_mem this
  change _ = 0 at hcount
  omega

/-- A wall numbered `2` between two empty cells is satisfied by a bulb on each end; the wall
also keeps the two bulbs from seeing each other. -/
private theorem numberedTwo_feasible : AkariFeasible [[0, 4, 0]] := by
  refine ⟨[(0, 0), (0, 2)], by decide, by decide, ?_, ?_, by decide⟩
  · intro r hr c hc h
    simp at hr hc
    subst hr
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
    · exact ⟨(0, 0), by simp, illuminates_self _ 0 0⟩
    · simp at h
    · exact ⟨(0, 2), by simp, illuminates_self _ 0 2⟩
  · intro b hb b' hb' hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact wall_blocks 4 (by decide)
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd (h 1 (by simp)) (by decide)
      · simp at h
    · exact absurd rfl hne

/-- Two bulbs in one open row see each other: `0, 0` admits one bulb, not two. -/
example : Illuminates [[0, 0]] 0 0 0 1 := Or.inl ⟨rfl, fun cc h => by simp at h; omega⟩

/-- The empty board and a board of plain walls are well formed and need no bulbs. -/
private theorem empty_feasible : AkariFeasible [] :=
  ⟨[], by decide, by decide, by intro r hr; simp at hr, by simp, by intro r hr; simp at hr⟩

example : WellFormed ([] : AkariInstance) := by unfold WellFormed; decide

example : WellFormed [[0, 4, 0]] := by unfold WellFormed; decide

/-- Malformed: an entry above `6` (a wall numbered `5`, more than four neighbours). -/
example : ¬ WellFormed [[7]] := by unfold WellFormed; decide

/-- Malformed: rows of different lengths. Only cells within the first row's width count, so
this all-wall board is still feasible with no bulbs. -/
private abbrev ragged : AkariInstance := [[1], [1, 1]]

private theorem ragged_malformed : ¬ WellFormed ragged := by unfold WellFormed; decide

private theorem ragged_feasible : AkariFeasible ragged := by
  refine ⟨[], by decide, by simp, ?_, by simp, ?_⟩
  · intro r hr c hc h
    simp at hr hc
    subst hc
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> simp at h
  · intro r hr c hc h
    simp at hr hc
    subst hc
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> simp at h

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the single empty cell and the wall numbered `2`. -/
example : akariDec (bitEncode ([[0]] : AkariInstance)) = true := by
  have hw : WellFormed ([[0]] : AkariInstance) := by unfold WellFormed; decide
  simp [akariDec, hw, single_feasible]

example : akariDec (bitEncode ([[0, 4, 0]] : AkariInstance)) = true := by
  have hw : WellFormed ([[0, 4, 0]] : AkariInstance) := by unfold WellFormed; decide
  simp [akariDec, hw, numberedTwo_feasible]

/-- It accepts the empty board. -/
example : akariDec (bitEncode ([] : AkariInstance)) = true := by
  have hw : WellFormed ([] : AkariInstance) := by unfold WellFormed; decide
  simp [akariDec, hw, empty_feasible]

/-- It rejects the well-formed wall numbered `1`. -/
example : akariDec (bitEncode ([[0, 3, 0]] : AkariInstance)) = false := by
  simp [akariDec, numberedOne_infeasible]

/-- It rejects the feasible ragged board. -/
example : akariDec (bitEncode ragged) = false := by
  simp [akariDec, ragged_malformed]

example : AkariFeasible ragged := ragged_feasible

/-- It rejects the bitstring `[true]`, which decodes to no board. -/
example : akariDec [true] = false := by
  have h : bitDecode (α := AkariInstance) [true] = none := by decide
  simp [akariDec, h]

end MetaMathlibExt.Complexity.NPComplete.Akari
