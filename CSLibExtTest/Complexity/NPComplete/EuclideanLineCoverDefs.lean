/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EuclideanLineCoverDefs

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (toInt)

private theorem dec_bitEncode (i : EuclideanLineCoverInstance) :
    euclideanLineCoverDec (bitEncode i) = true ↔
      WellFormed i ∧ EuclideanLineCoverFeasible i := by
  simp [euclideanLineCoverDec, bitDecode_bitEncode]

/-- The lines `x = 0` and `y = 0` are distinct and both pass through the one point `(0, 0)`. -/
example :
    euclideanLineCoverDec
      (bitEncode (([((1, 0), (0, 0), (0, 0)), ((0, 0), (1, 0), (0, 0))], 1) :
        EuclideanLineCoverInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨⟨by simp [toInt], ?_, by decide⟩, fun _ => (0, 0), ?_⟩
  · have hne : lineSet ((1, 0), (0, 0), (0, 0)) ≠ lineSet ((0, 0), (1, 0), (0, 0)) := by
      intro h
      have h01 : ((0 : ℝ), (1 : ℝ)) ∈ lineSet ((1, 0), (0, 0), (0, 0)) := by
        simp [lineSet, toInt]
      rw [h] at h01
      simp [lineSet, toInt] at h01
    simpa using hne
  · intro ℓ hℓ
    refine ⟨0, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl <;> simp [lineSet, toInt]

/-- The parallel lines `x = 0` and `x = 1` share no point, so one point cannot cover both. -/
example :
    euclideanLineCoverDec
      (bitEncode (([((1, 0), (0, 0), (0, 0)), ((1, 0), (0, 0), (1, 0))], 1) :
        EuclideanLineCoverInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, q, hq⟩
  obtain ⟨j, hj⟩ := hq ((1, 0), (0, 0), (0, 0)) (by simp)
  obtain ⟨k, hk⟩ := hq ((1, 0), (0, 0), (1, 0)) (by simp)
  rw [Subsingleton.elim k j] at hk
  simp [lineSet, toInt] at hj hk
  linarith

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := EuclideanLineCoverInstance) bits = none) :
    euclideanLineCoverDec bits = false := by
  simp [euclideanLineCoverDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : euclideanLineCoverDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover
