/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetBasisDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetBasis

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SetBasisInstance) :
    setBasisDec (bitEncode i) = true ↔ WellFormed i ∧ SetBasisFeasible i := by
  simp [setBasisDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setBasisDec [true] = false := by
  have h : bitDecode (α := SetBasisInstance) [true] = none := rfl
  simp [setBasisDec, h]

/-- The basis `{0, 1}`, `{1, 2}` generates the three members, `{0, 1, 2}` as their union. -/
example :
    setBasisDec (bitEncode ((3, [[0, 1], [1, 2], [0, 1, 2]], 2) : SetBasisInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {toSubset 3 [0, 1], toSubset 3 [1, 2]}, by decide, ?_⟩
  unfold toSubset
  decide

/-- A one-set basis would have to equal both `{0, 1}` and `{1, 2}`. -/
example :
    setBasisDec (bitEncode ((3, [[0, 1], [1, 2], [0, 1, 2]], 1) : SetBasisInstance)) = false := by
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

/-- A member listed out of increasing order is malformed. -/
example :
    setBasisDec (bitEncode ((3, [[1, 0]], 1) : SetBasisInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.SetBasis
