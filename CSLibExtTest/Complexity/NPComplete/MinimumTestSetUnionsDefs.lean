/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumTestSetUnionsDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.MinimumTestSet (MinimumTestSetInstance)

private theorem accepts_encoding (i : MinimumTestSetInstance) :
    minimumTestSetUnionsDec (bitEncode i) = true ↔
      WellFormed i ∧ MinimumTestSetUnionsFeasible i := by
  simp [minimumTestSetUnionsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumTestSetUnionsDec [true] = false := by
  have h : bitDecode (α := MinimumTestSetInstance) [true] = none := rfl
  simp [minimumTestSetUnionsDec, h]

set_option synthInstance.maxSize 4096 in
/-- The unions `{0} ∪ {1}` and `{0} ∪ {2}` distinguish every pair of `{0, 1, 2, 3}`; two of the
singleton tests alone would leave a pair undistinguished. -/
example :
    minimumTestSetUnionsDec
      (bitEncode ((4, [[0], [1], [2]], 2) : MinimumTestSetInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed MinimumTestSet.WellFormed; decide, [[[0], [1]], [[0], [2]]],
    by decide, by decide, by decide⟩

/-- One union test splits `{0, 1, 2}` into two sides, so some pair stays together. -/
example :
    minimumTestSetUnionsDec (bitEncode ((3, [[0], [1]], 1) : MinimumTestSetInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨T, -, hlen, hd⟩ := ((accepts_encoding _).1 h).2
  match T, hlen with
  | [], _ =>
    obtain ⟨t, ht, -⟩ := hd 0 (by decide) 1 (by decide) (by decide)
    simp at ht
  | [t], _ =>
    obtain ⟨t₁, ht₁, h₀₁⟩ := hd 0 (by decide) 1 (by decide) (by decide)
    obtain ⟨t₂, ht₂, h₀₂⟩ := hd 0 (by decide) 2 (by decide) (by decide)
    obtain ⟨t₃, ht₃, h₁₂⟩ := hd 1 (by decide) 2 (by decide) (by decide)
    simp only [List.mem_singleton] at ht₁ ht₂ ht₃
    subst ht₁ ht₂ ht₃
    clear hd
    generalize (∃ s ∈ t₃, 0 ∈ s) = p₀ at h₀₁ h₀₂
    generalize (∃ s ∈ t₃, 1 ∈ s) = p₁ at h₀₁ h₁₂
    generalize (∃ s ∈ t₃, 2 ∈ s) = p₂ at h₀₂ h₁₂
    tauto
  | _ :: _ :: _, hlen => simp at hlen

/-- Listing the test `{1}` twice is malformed. -/
example :
    minimumTestSetUnionsDec
      (bitEncode ((3, [[0], [1], [1]], 2) : MinimumTestSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2.1
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions
