/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DistanceDPartitionPointsPlaneDefs

namespace MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)

private theorem dec_bitEncode (i : DistanceDPartitionPointsPlaneInstance) :
    distanceDPartitionPointsPlaneDec (bitEncode i) = true ↔
      WellFormed i ∧ DistanceDPartitionPointsPlaneFeasible i := by
  simp [distanceDPartitionPointsPlaneDec, bitDecode_bitEncode]

/-- The points `(0, 0)` and `(2, 0)` are at distance `2 > d = 1`, so one set holds both. -/
example :
    distanceDPartitionPointsPlaneDec
      (bitEncode (([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1, 1) :
        DistanceDPartitionPointsPlaneInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, fun _ => 0, fun b => ⟨0, Subsingleton.elim _ _⟩,
    ?_⟩
  unfold point toInt
  decide

/-- The points `(0, 0)` and `(1, 0)` are at distance `1 = d`, so they cannot share the single
set. -/
example :
    distanceDPartitionPointsPlaneDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0))], 1, 1) :
        DistanceDPartitionPointsPlaneInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, c, -, h⟩
  have := h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (Subsingleton.elim _ _)
  revert this
  unfold point toInt
  decide

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := DistanceDPartitionPointsPlaneInstance) bits = none) :
    distanceDPartitionPointsPlaneDec bits = false := by
  simp [distanceDPartitionPointsPlaneDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : distanceDPartitionPointsPlaneDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane
