/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornCFiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite
open scoped Simplicial
open SSet SSet.Rezk

namespace SegalOuterHornCFiltrationTest

private def firstFace : outerHornCFaceIndex 1 := ⟨{0, 1, 2}, by decide⟩
private def otherFace : outerHornCFaceIndex 1 := ⟨{0, 1, 3}, by decide⟩

-- Sorting does not change the original inclusion category.
private theorem testContract01 : ¬ firstFace ≤ otherFace := by decide
private theorem testContract02 : ¬ otherFace ≤ firstFace := by decide

private theorem testContract03 (m : ℕ) (S : outerHornCFaceIndex m) :
    outerHornCEnumeration m ((outerHornCEnumeration m).symm S) = S :=
  outerHornCEnumeration_apply_symm m S

private theorem testContract04 (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (outerHornCEnumeration m).symm (outerHornCEnumeration m i) = i :=
  outerHornCEnumeration_symm_apply m i

private theorem testContract05 (m : ℕ) {i j : Fin (Fintype.card (outerHornCFaceIndex m))} (h : i ≤ j) :
    (outerHornCEnumeration m i).val.card ≤ (outerHornCEnumeration m j).val.card :=
  outerHornCEnumeration_card_mono m h

private theorem testContract06 (m : ℕ) : outerHornCStage.{u} m 0 = outerHornCU m := outerHornCStage_zero m

private theorem testContract07 (m : ℕ) :
    outerHornCStage.{u} m (Fintype.card (outerHornCFaceIndex m)) = outerHornC (m + 2) :=
  outerHornCStage_end m

private theorem testContract08 (n : ℕ) : outerHornCStage.{u} 0 n = outerHornCU 0 := outerHornCStage_low n

private theorem testContract09 (m : ℕ) :
    innerAnodyneExtensions (Subcomplex.homOfLE (outerHornCU_le_C.{u} m)) :=
  outerHornCU_to_C_innerAnodyne m

private theorem testContract10 (m n : ℕ) : SSet.Finite (outerHornCStage.{u + 1} m n : SSet.{u + 1}) :=
  inferInstance

private theorem testContract11 (m n : ℕ) : IsFinitelyPresentable.{u + 1}
    (outerHornCStage m n : SSet.{u + 1}) := inferInstance

-- Both original two-faces are actual inner-horn attachments, irrespective of their tie order.
private theorem testContract12 :
    2 ≤ outerHornCFaceDim (outerHornCEnumeration 1 ((outerHornCEnumeration 1).symm firstFace)) := by
  rw [outerHornCEnumeration_apply_symm]
  decide

private theorem testContract13 :
    2 ≤ outerHornCFaceDim (outerHornCEnumeration 1 ((outerHornCEnumeration 1).symm otherFace)) := by
  rw [outerHornCEnumeration_apply_symm]
  decide

section ArbitraryOriginalSquare

variable (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i))

include h2

private theorem testContract14 :
    (outerHornCStage.{u} m i.val).preimage (outerHornCFaceMap (outerHornCEnumeration m i)) =
      horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 :=
  outerHornCStage_face_preimage m i h2

private theorem testContract15 : IsPushout (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
    (outerHornCAttachment.{u} m i h2) (outerHornCFaceToNext m i) (outerHornCStageStep m i) :=
  outerHornCAttachment_isPushout m i h2

private theorem testContract16 :
    pushout.inl (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) ≫ (outerHornCAttachmentPushoutIso m i h2).hom =
      outerHornCFaceToNext m i := outerHornCAttachmentPushoutIso_inl m i h2

private theorem testContract17 :
    pushout.inr (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) ≫ (outerHornCAttachmentPushoutIso m i h2).hom =
      outerHornCStageStep m i := outerHornCAttachmentPushoutIso_inr m i h2

private theorem testContract18 : outerHornCFaceToNext.{u} m i ≫ (outerHornCAttachmentPushoutIso m i h2).inv =
    pushout.inl (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
      (outerHornCAttachment.{u} m i h2) := outerHornCAttachmentPushoutIso_face m i h2

private theorem testContract19 : outerHornCStageStep.{u} m i ≫ (outerHornCAttachmentPushoutIso m i h2).inv =
    pushout.inr (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
      (outerHornCAttachment.{u} m i h2) := outerHornCAttachmentPushoutIso_old m i h2

variable {X Y : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g)

private theorem testContract20 : outerHornCFaceToNext.{u} m i ≫ outerHornCAttachmentDesc m i h2 f g w = f :=
  outerHornCAttachmentDesc_face m i h2 f g w

private theorem testContract21 : outerHornCStageStep.{u} m i ≫ outerHornCAttachmentDesc m i h2 f g w = g :=
  outerHornCAttachmentDesc_old m i h2 f g w

private theorem testContract22 (d : (outerHornCStage m (i.val + 1) : SSet.{u}) ⟶ X)
    (hf : outerHornCFaceToNext m i ≫ d = f) (hg : outerHornCStageStep m i ≫ d = g) :
    d = outerHornCAttachmentDesc m i h2 f g w :=
  outerHornCAttachmentDesc_unique m i h2 f g w d hf hg

private theorem testContract23 (q : X ⟶ Y) : outerHornCAttachmentDesc.{u} m i h2 f g w ≫ q =
    outerHornCAttachmentDesc m i h2 (f ≫ q) (g ≫ q)
      (by simpa only [Category.assoc] using congrArg (fun h => h ≫ q) w) :=
  outerHornCAttachmentDesc_postcomp m i h2 f g w q

end ArbitraryOriginalSquare

section ActualInnerDiscreteSquare

variable (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i))
    {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment.{u} m i h2) ≫ g)

private theorem testContract24 (a b : SimplexCategoryᵒᵖ)
    (x : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}).obj a) :
    ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app b
      ((outerHornCFaceToNext m i).app a x) = (f.app a).app b x :=
  innerOuterHornCAttachmentDesc_face_app m i h2 f g w a b x

private theorem testContract25 (a b : SimplexCategoryᵒᵖ) (x : (outerHornCStage m i.val : SSet.{u}).obj a) :
    ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app b
      ((outerHornCStageStep m i).app a x) = (g.app a).app b x :=
  innerOuterHornCAttachmentDesc_old_app m i h2 f g w a b x

end ActualInnerDiscreteSquare

end SegalOuterHornCFiltrationTest
