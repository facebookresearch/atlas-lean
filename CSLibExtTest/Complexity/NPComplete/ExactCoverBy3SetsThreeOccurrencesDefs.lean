/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrencesDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ExactCoverBy3Sets (ExactCoverBy3SetsInstance ExactCoverBy3SetsFeasible)

/-- Unique membership in a list, with the uniqueness quantifier over list elements. -/
private theorem existsUnique_mem_iff (l : List (List ℕ)) (x : ℕ) :
    (∃! s ∈ l, x ∈ s) ↔ ∃ s ∈ l, x ∈ s ∧ ∀ t ∈ l, x ∈ t → t = s := by
  constructor
  · rintro ⟨s, ⟨hs, hx⟩, h⟩
    exact ⟨s, hs, hx, fun t ht hxt => h t ⟨ht, hxt⟩⟩
  · rintro ⟨s, hs, hx, h⟩
    exact ⟨s, ⟨hs, hx⟩, fun t ⟨ht, hxt⟩ => h t ht hxt⟩

/-- Feasibility ranges over the finitely many sublists of the candidate list. -/
private theorem feasible_iff (i : ExactCoverBy3SetsInstance) :
    ExactCoverBy3SetsFeasible i ↔
      ∃ sub ∈ i.2.sublists, ∀ x < 3 * i.1, ∃ s ∈ sub, x ∈ s ∧ ∀ t ∈ sub, x ∈ t → t = s := by
  simp only [ExactCoverBy3SetsFeasible, List.mem_sublists, existsUnique_mem_iff]

/-- Three sorted triples over `{0, …, 5}`; every element occurs at most twice. -/
private abbrev yes : ExactCoverBy3SetsInstance := (2, [[0, 1, 2], [1, 2, 3], [3, 4, 5]])

/-- Covering `0` forces `[0, 1, 2]` and covering `5` forces `[2, 4, 5]`, which both hold `2`. -/
private abbrev no : ExactCoverBy3SetsInstance := (2, [[0, 1, 2], [1, 2, 3], [2, 4, 5]])

/-- Element `0` occurs in four triples, although the first two triples are an exact cover. -/
private abbrev fourOccurrences : ExactCoverBy3SetsInstance :=
  (2, [[0, 1, 2], [3, 4, 5], [0, 1, 3], [0, 1, 4], [0, 1, 5]])

/-- The decision problem accepts `yes`, with witness `[[0, 1, 2], [3, 4, 5]]`. -/
example : exactCoverBy3SetsThreeOccurrencesDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed ExactCoverBy3Sets.WellFormed; decide
  have hf : ExactCoverBy3SetsFeasible yes := by
    refine ⟨[[0, 1, 2], [3, 4, 5]], by decide, ?_⟩
    simp only [existsUnique_mem_iff]
    decide
  simp [exactCoverBy3SetsThreeOccurrencesDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`, which has no exact cover. -/
example : WellFormed no ∧ exactCoverBy3SetsThreeOccurrencesDec (bitEncode no) = false := by
  have hw : WellFormed no := by unfold WellFormed ExactCoverBy3Sets.WellFormed; decide
  have hf : ¬ ExactCoverBy3SetsFeasible no := by rw [feasible_iff]; decide
  exact ⟨hw, by simp [exactCoverBy3SetsThreeOccurrencesDec, bitDecode_bitEncode, hf]⟩

/-- The occurrence bound is what rejects `fourOccurrences`: it is a well-formed, feasible
EXACT COVER BY 3-SETS instance, yet this decision problem rejects it. -/
example :
    ExactCoverBy3Sets.WellFormed fourOccurrences ∧ ExactCoverBy3SetsFeasible fourOccurrences ∧
      exactCoverBy3SetsThreeOccurrencesDec (bitEncode fourOccurrences) = false := by
  have hw : ¬ WellFormed fourOccurrences := by
    unfold WellFormed ExactCoverBy3Sets.WellFormed; decide
  refine ⟨by unfold ExactCoverBy3Sets.WellFormed; decide, ⟨[[0, 1, 2], [3, 4, 5]], by decide, ?_⟩,
    by simp [exactCoverBy3SetsThreeOccurrencesDec, bitDecode_bitEncode, hw]⟩
  simp only [existsUnique_mem_iff]
  decide

/-- A triple listed out of increasing order is malformed. -/
example : ¬ WellFormed ((1, [[1, 0, 2]]) : ExactCoverBy3SetsInstance) := by
  unfold WellFormed ExactCoverBy3Sets.WellFormed; decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : exactCoverBy3SetsThreeOccurrencesDec [true] = false := by
  have h : bitDecode (α := ExactCoverBy3SetsInstance) [true] = none := rfl
  simp [exactCoverBy3SetsThreeOccurrencesDec, h]

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences
