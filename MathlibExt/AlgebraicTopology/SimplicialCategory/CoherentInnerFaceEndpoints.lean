/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentTwoOutsideFaces

/-!
# The original outer endpoints in common nonendpoint ordinal faces

Two distinct interior omitted vertices induce two actual interior face
operators in their supplied faces. Each keeps the original first and
last source vertices. Their common ordinal embedding therefore retains
exactly the original outer endpoints, including all lifted universes.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.InnerFaceEndpoints
open HornBoxFaces
variable {n : ℕ} (j k : Interior.{u} n) (hjk : HornBoxFaces.vertex j < HornBoxFaces.vertex k)

/-- The first common-face omitted index is still a genuine source interior index. -/
theorem pred_ne_zero : (HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (HornBoxFaces.vertex k).val - 1 = 0 at hv
  have hj₀ : 0 < (HornBoxFaces.vertex j).val := j.property.1
  have hjk' : (HornBoxFaces.vertex j).val < (HornBoxFaces.vertex k).val := hjk
  omega

/-- The same first common-face omitted index is distinct from its source last vertex. -/
theorem pred_ne_last : (HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk) ≠ Fin.last (n + 1) := by
  intro h
  have hv := congrArg Fin.val h
  change (HornBoxFaces.vertex k).val - 1 = n + 1 at hv
  have hkₙ : (HornBoxFaces.vertex k).val < n + 2 := k.property.2
  omega

/-- The other common-face omitted index is distinct from its source first vertex. -/
theorem castPred_ne_zero : (HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (HornBoxFaces.vertex j).val = 0 at hv
  have hj₀ : 0 < (HornBoxFaces.vertex j).val := j.property.1
  omega

/-- The other common-face omitted index is distinct from its source last vertex. -/
theorem castPred_ne_last : (HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk) ≠ Fin.last (n + 1) := by
  intro h
  have hv := congrArg Fin.val h
  change (HornBoxFaces.vertex j).val = n + 1 at hv
  have hkₙ : (HornBoxFaces.vertex k).val < n + 2 := k.property.2
  have hjk' : (HornBoxFaces.vertex j).val < (HornBoxFaces.vertex k).val := hjk
  omega

/-- The first actual common ordinal source face keeps its individual zero vertex. -/
theorem left_zero : ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)).succAbove (0 : Fin (n + 1)) = 0 :=
  Fin.succAbove_ne_zero_zero (pred_ne_zero j k hjk)

/-- The first actual common ordinal source face keeps its individual last vertex. -/
theorem left_last : ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)).succAbove (Fin.last n) = Fin.last (n + 1) :=
  Fin.succAbove_ne_last_last (pred_ne_last j k hjk)

/-- The other actual common ordinal source face keeps the same zero vertex. -/
theorem right_zero : ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)).succAbove (0 : Fin (n + 1)) = 0 :=
  Fin.succAbove_ne_zero_zero (castPred_ne_zero j k hjk)

/-- The other actual common ordinal source face keeps the same last vertex. -/
theorem right_last : ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)).succAbove (Fin.last n) =
    Fin.last (n + 1) :=
  Fin.succAbove_ne_last_last (castPred_ne_last j k hjk)

/-- The common original ordinal chart retains the actual first outer endpoint. -/
theorem common_zero :
    TwoOutsideFaces.point (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up (0 : Fin (n + 1))) =
      (ULift.up 0 : ULift.{u} (Fin (n + 3))) := by
  apply ULift.ext
  change (HornBoxFaces.vertex j).succAbove
    (((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)).succAbove 0) = 0
  rw [left_zero j k hjk, HornBoxFaces.source_zero j]

/-- The same common original chart retains the actual last outer endpoint. -/
theorem common_last :
    TwoOutsideFaces.point (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up (Fin.last n)) =
      (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) := by
  apply ULift.ext
  change (HornBoxFaces.vertex j).succAbove
    (((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)).succAbove (Fin.last n)) = Fin.last (n + 2)
  rw [left_last j k hjk, HornBoxFaces.target_last j]

end CategoryTheory.CoherentRealization.InnerFaceEndpoints
