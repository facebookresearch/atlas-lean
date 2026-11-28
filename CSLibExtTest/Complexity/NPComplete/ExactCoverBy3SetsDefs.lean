/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExactCoverBy3SetsDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem dec_bitEncode (i : ExactCoverBy3SetsInstance) :
    exactCoverBy3SetsDec (bitEncode i) = true ↔ WellFormed i ∧ ExactCoverBy3SetsFeasible i := by
  simp [exactCoverBy3SetsDec, bitDecode_bitEncode]

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

/-- The universe `{0, …, 5}` with three triples; the first and last are an exact cover. -/
private abbrev yes : ExactCoverBy3SetsInstance := (2, [[0, 1, 2], [1, 2, 3], [3, 4, 5]])

/-- Covering `0` forces `[0, 1, 2]` and covering `5` forces `[2, 4, 5]`, which both hold `2`. -/
private abbrev no : ExactCoverBy3SetsInstance := (2, [[0, 1, 2], [1, 2, 3], [2, 4, 5]])

/-- The decision problem accepts `yes`, with witness `[[0, 1, 2], [3, 4, 5]]`. -/
example : exactCoverBy3SetsDec (bitEncode yes) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, ?_⟩
  refine ⟨[[0, 1, 2], [3, 4, 5]], by decide, ?_⟩
  simp only [existsUnique_mem_iff]
  decide

/-- The decision problem rejects the well-formed instance `no`, which has no exact cover. -/
example : exactCoverBy3SetsDec (bitEncode no) = false := by
  have hw : WellFormed no := by unfold WellFormed; decide
  have hf : ¬ ExactCoverBy3SetsFeasible no := by rw [feasible_iff]; decide
  simp [exactCoverBy3SetsDec, bitDecode_bitEncode, hf]

/-- An entry with a repeated element is not a 3-set. The instance `(1, [[0, 1, 2], [0, 0, 1]])`
is feasible via `[[0, 1, 2]]`, yet the decision problem rejects it as malformed. -/
example :
    ExactCoverBy3SetsFeasible ((1, [[0, 1, 2], [0, 0, 1]]) : ExactCoverBy3SetsInstance) ∧
      exactCoverBy3SetsDec
        (bitEncode ((1, [[0, 1, 2], [0, 0, 1]]) : ExactCoverBy3SetsInstance)) = false := by
  have hw : ¬ WellFormed ((1, [[0, 1, 2], [0, 0, 1]]) : ExactCoverBy3SetsInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨[[0, 1, 2]], by decide, ?_⟩, ?_⟩
  · simp only [existsUnique_mem_iff]
    decide
  · simp [exactCoverBy3SetsDec, bitDecode_bitEncode, hw]

/-- A lone continuation bit is a truncated instance encoding. -/
example : exactCoverBy3SetsDec [true] = false := by
  have h : bitDecode (α := ExactCoverBy3SetsInstance) [true] = none := rfl
  simp [exactCoverBy3SetsDec, h]

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets
