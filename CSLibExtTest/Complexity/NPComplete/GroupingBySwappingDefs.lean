/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GroupingBySwappingDefs

namespace MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : GroupingBySwappingInstance) :
    groupingBySwappingDec (bitEncode i) = true ↔ WellFormed i ∧ GroupingBySwappingFeasible i := by
  simp [groupingBySwappingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : groupingBySwappingDec [true] = false := by
  have h : bitDecode (α := GroupingBySwappingInstance) [true] = none := rfl
  simp [groupingBySwappingDec, h]

/-- A string of length three with no pattern `a b a` is grouped. -/
private theorem grouped_of_three {x y z : ℕ} (h : x = y ∨ y = z) : IsGrouped [x, y, z] := by
  intro a b hab hs
  have := hs.eq_of_length (by simp)
  simp only [List.cons.injEq, and_true] at this
  omega

/-- The string `0 1 0` becomes the grouped string `0 0 1` with one interchange. -/
example : groupingBySwappingDec (bitEncode ((2, [0, 1, 0], 1) : GroupingBySwappingInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    [[0, 1, 0], [0, 0, 1]], [0, 0, 1], rfl, rfl, by simp, ?_, grouped_of_three (by simp)⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨[0], [], 1, 0, rfl, rfl⟩

/-- The string `0 1 1 0` is not grouped, and none of the three strings one interchange away is
grouped either, so a bound of one interchange is too small. -/
example : groupingBySwappingDec (bitEncode ((2, [0, 1, 1, 0], 1) : GroupingBySwappingInstance)) =
    false := by
  have start : ¬ IsGrouped [0, 1, 1, 0] := fun hg => hg 0 1 (by decide) (by decide)
  have step : ∀ w, Swap [0, 1, 1, 0] w → ¬ IsGrouped w := by
    rintro w ⟨l₁, l₂, c, d, hx, rfl⟩ hg
    rcases l₁ with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, l₁⟩⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact hg 1 0 (by decide) (by decide)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      exact hg 0 1 (by decide) (by decide)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
      exact hg 0 1 (by decide) (by decide)
    · have := congrArg List.length hx
      simp only [List.length_cons, List.length_append, List.length_nil] at this
      omega
  have h : ¬ GroupingBySwappingFeasible (2, [0, 1, 1, 0], 1) := by
    rintro ⟨ws, y, hhead, hlast, hlen, hchain, hgroup⟩
    rcases ws with _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, ws⟩⟩⟩
    · simp at hhead
    · simp at hhead hlast
      subst hhead hlast
      exact start hgroup
    · simp at hhead hlast
      subst hhead hlast
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hchain
      exact step _ hchain hgroup
    · simp at hlen
  simpa [groupingBySwappingDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping
