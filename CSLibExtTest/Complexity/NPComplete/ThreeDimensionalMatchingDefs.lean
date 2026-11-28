/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ThreeDimensionalMatchingInstance) :
    threeDimensionalMatchingDec (bitEncode i) = true ↔
      WellFormed i ∧ ThreeDimensionalMatchingFeasible i := by
  simp [threeDimensionalMatchingDec, bitDecode_bitEncode]

/-- A list entry is the unique one with a property when exactly one entry has it. -/
private theorem existsUnique_of_filter {l : List (ℕ × ℕ × ℕ)} {p : ℕ × ℕ × ℕ → Prop}
    [DecidablePred p] (h : (l.filter fun t => decide (p t)).length = 1) : ∃! t ∈ l, p t := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 h
  have hmem : ∀ t, t ∈ l ∧ p t ↔ t = x := by
    intro t
    rw [← List.mem_singleton, ← hx, List.mem_filter, decide_eq_true_iff]
  exact ⟨x, (hmem x).2 rfl, fun t ht => (hmem t).1 ht⟩

/-- Feasibility forces every coordinate value to occur in a sublist of length `q`. -/
private theorem feasible_imp (i : ThreeDimensionalMatchingInstance)
    (h : ThreeDimensionalMatchingFeasible i) : ∃ m ∈ i.2.sublists, m.length = i.1 ∧
      ∀ a < i.1, (∃ t ∈ m, t.1 = a) ∧ (∃ t ∈ m, t.2.1 = a) ∧ ∃ t ∈ m, t.2.2 = a := by
  obtain ⟨m, hsub, hlen, h₁, h₂, h₃⟩ := h
  refine ⟨m, List.mem_sublists.2 hsub, hlen, fun a ha => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨t, ⟨ht, hta⟩, -⟩ := h₁ a ha
    exact ⟨t, ht, hta⟩
  · obtain ⟨t, ⟨ht, hta⟩, -⟩ := h₂ a ha
    exact ⟨t, ht, hta⟩
  · obtain ⟨t, ⟨ht, hta⟩, -⟩ := h₃ a ha
    exact ⟨t, ht, hta⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : threeDimensionalMatchingDec [true] = false := by
  have h : bitDecode (α := ThreeDimensionalMatchingInstance) [true] = none := rfl
  simp [threeDimensionalMatchingDec, h]

/-- The triples `(0, 0, 0)` and `(1, 1, 1)` form a perfect matching; `(0, 1, 1)` is left out. -/
example :
    threeDimensionalMatchingDec
      (bitEncode ((2, [(0, 0, 0), (1, 1, 1), (0, 1, 1)]) : ThreeDimensionalMatchingInstance)) =
        true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [(0, 0, 0), (1, 1, 1)], by decide, by decide,
    ?_, ?_, ?_⟩ <;>
  · intro a ha
    apply existsUnique_of_filter
    revert a
    decide

/-- Every two of the three triples collide in some coordinate. -/
example :
    threeDimensionalMatchingDec
      (bitEncode ((2, [(0, 0, 0), (1, 1, 0), (0, 1, 1)]) : ThreeDimensionalMatchingInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := feasible_imp _ ((accepts_encoding _).1 h).2
  revert hf
  decide

/-- A coordinate equal to the part size is out of range. -/
example :
    threeDimensionalMatchingDec
      (bitEncode ((1, [(0, 1, 0)]) : ThreeDimensionalMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
