/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarDeformation
public import MathlibExt.Topology.Category.TopPair.PointQuotient

/-!
# Point quotients of actual cell-family attachments

The literal family of boundary-to-disk inclusions maps to the pair formed by
the original-space inclusion in its actual attachment pushout.  Collapsing the
original space in that attachment leaves exactly the point quotient of the
literal disk family.  This file constructs the resulting pointed isomorphism
from the two genuine pushout squares and records its exact formulas on the
disk-family projection and distinguished point.

No homology, cellular boundary, spherical representative, or plus-construction
claim is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellFamilyAttachment

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The literal disk-family pair maps to the actual attachment pair by the
disk inclusion on ambient spaces and the attaching map on boundaries. -/
def literalToAttachmentPair :
    literalPair ι n ⟶ CellCollarDeformation.attachmentPair X n a :=
  TopPair.ofHom (diskInclusion X n a) (attachingMap X n a)
    (isPushout X n a).w.symm

@[simp]
theorem literalToAttachmentPair_fst :
    TopPair.Hom.fst (literalToAttachmentPair X n a) = diskInclusion X n a :=
  rfl

@[simp]
theorem literalToAttachmentPair_snd :
    TopPair.Hom.snd (literalToAttachmentPair X n a) = attachingMap X n a :=
  rfl

/-- The point-quotient square for the actual attachment pair. -/
private theorem actualPointQuotient_isPushout :
    IsPushout
      (CellCollarDeformation.attachmentPair X n a).map
      (TopCat.isTerminalPUnit.from
        (CellCollarDeformation.attachmentPair X n a).snd)
      (TopCat.pointQuotientProjection.app
        ((forgetToArrow).obj (CellCollarDeformation.attachmentPair X n a)))
      (TopCat.pointQuotientPoint
        ((forgetToArrow).obj (CellCollarDeformation.attachmentPair X n a))) :=
  IsPushout.of_hasPushout _ _

/-- Pasting the actual cell-attachment square with its point-quotient square
exhibits the collapsed attachment as a pushout of the literal boundaries into
the literal disks and a point. -/
theorem collapsedAttachment_isPushout :
    IsPushout
      (boundaryToDisks ι n)
      (TopCat.isTerminalPUnit.from (boundaries ι n))
      (diskInclusion X n a ≫
        TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj (CellCollarDeformation.attachmentPair X n a)))
      (TopCat.pointQuotientPoint
        ((forgetToArrow).obj (CellCollarDeformation.attachmentPair X n a))) := by
  have h := (isPushout X n a).paste_vert
    (actualPointQuotient_isPushout X n a)
  have hterminal :
      attachingMap X n a ≫
          TopCat.isTerminalPUnit.from
            (CellCollarDeformation.attachmentPair X n a).snd =
        TopCat.isTerminalPUnit.from (boundaries ι n) := by
    exact TopCat.isTerminalPUnit.hom_ext _ _
  rw [hterminal] at h
  exact h

/-- The canonical point-quotient square for the literal disk-family pair. -/
theorem literalPointQuotient_isPushout :
    IsPushout
      (boundaryToDisks ι n)
      (TopCat.isTerminalPUnit.from (boundaries ι n))
      (TopCat.pointQuotientProjection.app
        ((forgetToArrow).obj (literalPair ι n)))
      (TopCat.pointQuotientPoint ((forgetToArrow).obj (literalPair ι n))) :=
  IsPushout.of_hasPushout _ _

/-- Collapsing the original space in its actual cell-family attachment is
canonically the point quotient of the literal disk family.  The forward map
is oriented from the literal quotient to the collapsed actual attachment. -/
noncomputable def attachmentPointQuotientIso :
    TopPair.pointQuotientFunctor.obj (literalPair ι n) ≅
      TopPair.pointQuotientFunctor.obj
        (CellCollarDeformation.attachmentPair X n a) :=
  Under.isoMk
    ((collapsedAttachment_isPushout X n a).isoIsPushout _ _
      (literalPointQuotient_isPushout (ι := ι) n)).symm
    (by
      exact ((collapsedAttachment_isPushout X n a).inr_isoIsPushout_inv
        _ _ (literalPointQuotient_isPushout (ι := ι) n)))

/-- The forward quotient isomorphism sends the literal disk projection to the
actual disk inclusion followed by the actual collapse. -/
@[reassoc]
theorem pointQuotientProjection_comp_attachmentPointQuotientIso_hom :
    TopCat.pointQuotientProjection.app ((forgetToArrow).obj (literalPair ι n)) ≫
        (attachmentPointQuotientIso X n a).hom.right =
      diskInclusion X n a ≫
        TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj
            (CellCollarDeformation.attachmentPair X n a)) := by
  have h := (collapsedAttachment_isPushout X n a).inl_isoIsPushout_inv
    _ _ (literalPointQuotient_isPushout (ι := ι) n)
  change
    TopCat.pointQuotientProjection.app ((forgetToArrow).obj (literalPair ι n)) ≫
        (attachmentPointQuotientIso X n a).hom.right =
      diskInclusion X n a ≫
        TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj
            (CellCollarDeformation.attachmentPair X n a)) at h
  exact h

/-- The inverse quotient isomorphism sends the collapsed actual disk family
back to the literal disk-family projection. -/
@[reassoc]
theorem diskInclusion_pointQuotientProjection_comp_attachmentPointQuotientIso_inv :
    diskInclusion X n a ≫
        TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj
            (CellCollarDeformation.attachmentPair X n a)) ≫
        (attachmentPointQuotientIso X n a).inv.right =
      TopCat.pointQuotientProjection.app
        ((forgetToArrow).obj (literalPair ι n)) := by
  have h := (collapsedAttachment_isPushout X n a).inl_isoIsPushout_hom
    _ _ (literalPointQuotient_isPushout (ι := ι) n)
  change
    diskInclusion X n a ≫
        TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj
            (CellCollarDeformation.attachmentPair X n a)) ≫
        (attachmentPointQuotientIso X n a).inv.right =
      TopCat.pointQuotientProjection.app
        ((forgetToArrow).obj (literalPair ι n)) at h
  exact h

/-- The forward quotient isomorphism preserves the distinguished point. -/
@[reassoc (attr := simp)]
theorem pointQuotientPoint_comp_attachmentPointQuotientIso_hom :
    TopCat.pointQuotientPoint ((forgetToArrow).obj (literalPair ι n)) ≫
        (attachmentPointQuotientIso X n a).hom.right =
      TopCat.pointQuotientPoint
        ((forgetToArrow).obj
          (CellCollarDeformation.attachmentPair X n a)) := by
  exact (attachmentPointQuotientIso X n a).hom.w

/-- The inverse quotient isomorphism preserves the distinguished point. -/
@[reassoc (attr := simp)]
theorem pointQuotientPoint_comp_attachmentPointQuotientIso_inv :
    TopCat.pointQuotientPoint
          ((forgetToArrow).obj
            (CellCollarDeformation.attachmentPair X n a)) ≫
        (attachmentPointQuotientIso X n a).inv.right =
      TopCat.pointQuotientPoint ((forgetToArrow).obj (literalPair ι n)) := by
  exact (attachmentPointQuotientIso X n a).inv.w

set_option backward.isDefEq.respectTransparency false in
/-- The forward quotient isomorphism is exactly the functorial point-quotient
map induced by the literal-to-attachment pair morphism. -/
theorem attachmentPointQuotientIso_hom :
    (attachmentPointQuotientIso X n a).hom =
      TopPair.pointQuotientFunctor.map (literalToAttachmentPair X n a) := by
  apply Under.UnderMorphism.ext
  apply (literalPointQuotient_isPushout (ι := ι) n).hom_ext
  · have hIso :=
      pointQuotientProjection_comp_attachmentPointQuotientIso_hom X n a
    have hMap := TopCat.pointQuotientMap_inl
      ((forgetToArrow).map (literalToAttachmentPair X n a))
    change
      TopCat.pointQuotientProjection.app
            ((forgetToArrow).obj (literalPair ι n)) ≫
          (TopPair.pointQuotientFunctor.map
            (literalToAttachmentPair X n a)).right =
        diskInclusion X n a ≫
          TopCat.pointQuotientProjection.app
            ((forgetToArrow).obj
              (CellCollarDeformation.attachmentPair X n a)) at hMap
    exact hIso.trans hMap.symm
  · have hIso := pointQuotientPoint_comp_attachmentPointQuotientIso_hom X n a
    have hMap := TopCat.pointQuotientMap_inr
      ((forgetToArrow).map (literalToAttachmentPair X n a))
    exact hIso.trans hMap.symm

/-- The functorial point-quotient map of the actual pair morphism is an
isomorphism. -/
noncomputable instance pointQuotientFunctor_map_literalToAttachmentPair_isIso :
    IsIso (TopPair.pointQuotientFunctor.map
      (literalToAttachmentPair X n a)) := by
  rw [← attachmentPointQuotientIso_hom X n a]
  infer_instance

end AlgebraicTopology.CellFamilyAttachment

end

end
