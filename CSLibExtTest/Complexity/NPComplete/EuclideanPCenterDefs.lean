/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EuclideanPCenterDefs

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)

private theorem dec_bitEncode (i : EuclideanPCenterInstance) :
    euclideanPCenterDec (bitEncode i) = true ↔
      WellFormed i ∧ EuclideanPCenterFeasible i := by
  simp [euclideanPCenterDec, bitDecode_bitEncode]

/-- The points `(0, 0)` and `(2, 0)` lie within radius `1 / 1` of the one center `(1, 0)`. -/
example :
    euclideanPCenterDec
      (bitEncode (([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1, (1, 1)) :
        EuclideanPCenterInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, fun _ => (1, 0), ?_⟩
  intro q hq
  refine ⟨0, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> norm_num [point, toInt, radius]

/-- The points `(0, 0)` and `(3, 0)` are `3` apart, more than a diameter `2`, so no single disk
of radius `1 / 1` covers both. -/
example :
    euclideanPCenterDec
      (bitEncode (([((0, 0), (0, 0)), ((3, 0), (0, 0))], 1, (1, 1)) :
        EuclideanPCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, c, hc⟩
  obtain ⟨j, hj⟩ := hc ((0, 0), (0, 0)) (by simp)
  obtain ⟨k, hk⟩ := hc ((3, 0), (0, 0)) (by simp)
  rw [Subsingleton.elim k j] at hk
  norm_num [point, toInt, radius] at hj hk
  nlinarith [sq_nonneg (c j).2, sq_nonneg ((c j).1 - 3 / 2)]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := EuclideanPCenterInstance) bits = none) :
    euclideanPCenterDec bits = false := by
  simp [euclideanPCenterDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : euclideanPCenterDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter
