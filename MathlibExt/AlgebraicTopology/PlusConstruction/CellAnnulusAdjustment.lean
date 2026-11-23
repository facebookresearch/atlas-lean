/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusWeights

/-!
# Strict adjustment on the actual annular overlap

Adjust the constructed quotient-valued outer functor by the derived weights
on the actual collar overlap. The canonical overlap inclusion is injective on
objects, so the generic object-copy construction makes its restriction
strictly constant. Every point from the original source lies outside the
overlap image because the actual inner region has empty original-space
preimage. The adjustment therefore preserves every original-source arrow and
the exact original quotient homomorphism.

The actual inner functor is the literal constant functor, and its overlap
restriction agrees strictly with the adjusted outer restriction. No
outside-image, injectivity, difference, compatibility, global extension or
factorization witness is supplied as input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellAnnulusAdjustment

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]

/-- The actual canonical inclusion of the overlap groupoid into the outer-region groupoid. -/
def overlapInclusionFunctor :
    FundamentalGroupoid
        ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
          CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) ⥤
      FundamentalGroupoid
        (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)) :=
  FundamentalGroupoid.map
    (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
      (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
      (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)))

omit [P.Normal] in
/-- The actual subtype inclusion is injective on original overlap objects. -/
theorem overlapInclusion_obj_injective :
    Function.Injective (overlapInclusionFunctor X x P).obj := by
  intro c d h
  apply FundamentalGroupoid.ext
  apply Subtype.ext
  have hSub := congrArg FundamentalGroupoid.as h
  exact congrArg
    (fun z : ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)) => z.val)
    hSub

/-- The actual adjusted outer functor, using precisely the derived overlap weight. -/
def adjustedOuterFunctor :
    FundamentalGroupoid
        (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  CategoryTheory.SingleObj.objectAdjustment
    (overlapInclusionFunctor X x P)
    (CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P))
    (CellAnnulusWeights.overlapWeight X x P)

/-- The adjusted outer functor is strictly constant on the actual overlap. -/
theorem adjustedOuterFunctor_overlap :
    overlapInclusionFunctor X x P ⋙ adjustedOuterFunctor X x P =
      (Functor.const
        (FundamentalGroupoid
          ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
            CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)))).obj
        (SingleObj.star (FundamentalGroup X x ⧸ P)) := by
  apply CategoryTheory.SingleObj.comp_objectAdjustment_eq_const
  · exact overlapInclusion_obj_injective X x P
  · intro c d f
    change ((CellAnnulusWeights.overlapFunctor X x P).map f :
      FundamentalGroup X x ⧸ P) =
        CellAnnulusWeights.overlapWeight X x P d *
          (CellAnnulusWeights.overlapWeight X x P c)⁻¹
    exact CellAnnulusWeights.overlap_map_eq_difference X x P f

omit [P.Normal] in
/-- Every actual included original-space object lies outside the overlap object image. -/
theorem includedPoint_not_mem_range (y : X) :
    FundamentalGroupoid.mk
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P) y) ∉
      Set.range (overlapInclusionFunctor X x P).obj := by
  intro hy
  rcases hy with ⟨z, hz⟩
  have hSub :
      MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
          (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
          (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) z.as =
        CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P) y :=
    congrArg FundamentalGroupoid.as hz
  have hVal : z.as.val =
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) y).val :=
    congrArg Subtype.val hSub
  have hyV : CellFamilyAttachment.inclusion X 1
      (LoopCellAttachment.attachingMap X x P) y ∈
        CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P) := by
    rw [← CellCollarDeformation.inclusionU_val X 1
      (LoopCellAttachment.attachingMap X x P) y]
    rw [← hVal]
    exact z.as.property.2
  have hyPreimage : y ∈
      CellFamilyAttachment.inclusion X 1 (LoopCellAttachment.attachingMap X x P) ⁻¹'
        CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P) := hyV
  rw [CellCollarCover.inclusion_preimage_V] at hyPreimage
  exact hyPreimage.elim

omit [P.Normal] in
/-- In particular, the actual included original basepoint is outside the overlap image. -/
theorem includedBasepoint_not_mem_range :
    FundamentalGroupoid.mk
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P) x) ∉
      Set.range (overlapInclusionFunctor X x P).obj :=
  includedPoint_not_mem_range X x P x

/-- Every original-source arrow retains exactly its original outer-functor value. -/
theorem adjustedOuterFunctor_original_map
    {c d : FundamentalGroupoid X} (f : c ⟶ d) :
    ((adjustedOuterFunctor X x P).map
        ((FundamentalGroupoid.map
          (CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P)).hom).map f) :
      FundamentalGroup X x ⧸ P) =
        (CellQuotientFunctor.kappaU X x P 1
          (LoopCellAttachment.attachingMap X x P)).map
            ((FundamentalGroupoid.map
              (CellCollarDeformation.inclusionU X 1
                (LoopCellAttachment.attachingMap X x P)).hom).map f) := by
  apply CategoryTheory.SingleObj.objectAdjustment_map_of_not_mem_range
  · change FundamentalGroupoid.mk
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) c.as) ∉
        Set.range (overlapInclusionFunctor X x P).obj
    exact includedPoint_not_mem_range X x P c.as
  · change FundamentalGroupoid.mk
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) d.as) ∉
        Set.range (overlapInclusionFunctor X x P).obj
    exact includedPoint_not_mem_range X x P d.as

/-- Restriction along the actual original inclusion still recovers the exact
normalized quotient functor on the original groupoid. -/
theorem adjustedOuterFunctor_originalInclusion :
    FundamentalGroupoid.map
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P)).hom ⋙
      adjustedOuterFunctor X x P =
        Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P) := by
  calc
    _ = FundamentalGroupoid.map
          (CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P)).hom ⋙
        CellQuotientFunctor.kappaU X x P 1
          (LoopCellAttachment.attachingMap X x P) := by
      apply Functor.hext (fun _ => Subsingleton.elim _ _)
      intro c d f
      apply heq_of_eq
      exact adjustedOuterFunctor_original_map X x P f
    _ = _ := CellQuotientFunctor.kappaU_originalInclusion X x P 1
      (LoopCellAttachment.attachingMap X x P)

/-- At the included original basepoint, the adjusted and unadjusted End values agree exactly. -/
theorem adjustedOuterFunctor_includedEnd
    (e : FundamentalGroup
      (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) x)) :
    (((adjustedOuterFunctor X x P).mapEnd
      (FundamentalGroupoid.mk
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P) x))) e).asHom =
      ((CellQuotientFunctor.kappaU X x P 1
        (LoopCellAttachment.attachingMap X x P)).mapEnd
          (FundamentalGroupoid.mk
            (CellCollarDeformation.inclusionU X 1
              (LoopCellAttachment.attachingMap X x P) x)) e).asHom :=
  CategoryTheory.SingleObj.objectAdjustment_mapEnd_of_not_mem_range
    (overlapInclusionFunctor X x P)
    (CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P))
    (CellAnnulusWeights.overlapWeight X x P)
    (FundamentalGroupoid.mk
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) x))
    (includedBasepoint_not_mem_range X x P) e

/-- The exact original inclusion-based End homomorphism remains the original quotient map. -/
theorem adjustedOuterFunctor_originalInclusionEnd :
    ((SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.toMonoidHom.comp
      ((adjustedOuterFunctor X x P).mapEnd
        (FundamentalGroupoid.mk
          (CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P) x)))).comp
      (FundamentalGroup.mapOfEq
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P)).hom
        (rfl : CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P) x =
          CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P) x)) =
        QuotientGroup.mk' P := by
  apply MonoidHom.ext
  intro q
  have hPreserve := adjustedOuterFunctor_includedEnd X x P
    (FundamentalGroup.mapOfEq
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P)).hom rfl q)
  have hOriginal := DFunLike.congr_fun
    (CellQuotientFunctor.kappaU_originalInclusionEnd X x P 1
      (LoopCellAttachment.attachingMap X x P)) q
  change (((adjustedOuterFunctor X x P).mapEnd
    (FundamentalGroupoid.mk
      (CellCollarDeformation.inclusionU X 1
        (LoopCellAttachment.attachingMap X x P) x)))
          (FundamentalGroup.mapOfEq
            (CellCollarDeformation.inclusionU X 1
              (LoopCellAttachment.attachingMap X x P)).hom rfl q)).asHom =
    QuotientGroup.mk' P q
  change ((CellQuotientFunctor.kappaU X x P 1
    (LoopCellAttachment.attachingMap X x P)).mapEnd
      (FundamentalGroupoid.mk
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P) x))
        (FundamentalGroup.mapOfEq
          (CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P)).hom rfl q)).asHom =
      QuotientGroup.mk' P q at hOriginal
  exact hPreserve.trans hOriginal

/-- The actual inner functor is the literal constant quotient-valued functor. -/
def innerFunctor :
    FundamentalGroupoid
        (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  (Functor.const
    (FundamentalGroupoid
      (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)))).obj
    (SingleObj.star (FundamentalGroup X x ⧸ P))

/-- The literal inner functor restricts to the literal constant overlap functor. -/
theorem innerFunctor_overlap :
    FundamentalGroupoid.map
        (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterRight
          (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
          (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) ⋙
      innerFunctor X x P =
        (Functor.const
          (FundamentalGroupoid
            ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
              CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)))).obj
          (SingleObj.star (FundamentalGroup X x ⧸ P)) := by
  apply Functor.hext (fun _ => rfl)
  intro c d f
  apply heq_of_eq
  rfl

/-- The adjusted outer and literal inner functors agree strictly on the actual overlap. -/
theorem adjustedOuterFunctor_inner_compatibility :
    overlapInclusionFunctor X x P ⋙ adjustedOuterFunctor X x P =
      FundamentalGroupoid.map
        (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterRight
          (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
          (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) ⋙
        innerFunctor X x P :=
  (adjustedOuterFunctor_overlap X x P).trans (innerFunctor_overlap X x P).symm

end AlgebraicTopology.CellAnnulusAdjustment

end

end
