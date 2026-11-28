/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetBasisSizeThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.SetBasis (SetBasisInstance SetBasisFeasible toSubset)

private theorem accepts_encoding (i : SetBasisInstance) :
    setBasisSizeThreeDec (bitEncode i) = true ↔ WellFormed i ∧ SetBasisFeasible i := by
  simp [setBasisSizeThreeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setBasisSizeThreeDec [true] = false := by
  have h : bitDecode (α := SetBasisInstance) [true] = none := rfl
  simp [setBasisSizeThreeDec, h]

/-- The basis `{0, 1}`, `{1, 2}` generates the three members, `{0, 1, 2}` as their union. -/
example :
    setBasisSizeThreeDec
      (bitEncode ((3, [[0, 1], [1, 2], [0, 1, 2]], 2) : SetBasisInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed SetBasis.WellFormed; decide,
    {toSubset 3 [0, 1], toSubset 3 [1, 2]}, by decide, ?_⟩
  unfold toSubset
  decide

/-- A one-set basis would have to equal both `{0, 1}` and `{1, 2}`. -/
example :
    setBasisSizeThreeDec
      (bitEncode ((3, [[0, 1], [1, 2], [0, 1, 2]], 1) : SetBasisInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨B, hcard, hB⟩ := ((accepts_encoding _).1 h).2
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hcard
  have key : ∀ c ∈ ([[0, 1], [1, 2]] : List (List ℕ)), toSubset 3 c = b := by
    intro c hc
    obtain ⟨D, hD, hsup⟩ := hB c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; tauto)
    rcases Finset.subset_singleton_iff.1 hD with rfl | rfl
    · have hne : toSubset 3 c ≠ ∅ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide
      exact absurd hsup.symm hne
    · simpa using hsup.symm
  have h₁ := key [0, 1] (by simp)
  have h₂ := key [1, 2] (by simp)
  have : toSubset 3 [0, 1] ≠ toSubset 3 [1, 2] := by decide
  exact this (h₁.trans h₂.symm)

/-- The four-element member is outside the size-three restriction, although it is its own
basis. -/
example :
    setBasisSizeThreeDec (bitEncode ((4, [[0, 1, 2, 3]], 1) : SetBasisInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2 [0, 1, 2, 3] (by simp)
  revert hw
  decide

/-- The same four-element member is its own one-set basis in unrestricted SET BASIS. -/
example : SetBasisFeasible ((4, [[0, 1, 2, 3]], 1) : SetBasisInstance) := by
  refine ⟨{toSubset 4 [0, 1, 2, 3]}, by decide, ?_⟩
  unfold toSubset
  decide

end MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree
