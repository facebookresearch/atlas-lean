/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeCofibrations
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategoryZero

/-!
# The zero-object axiom for genuine cofiber-sequence cofibrations

Maps from the existing zero object of the cofiber-sequence category satisfy
the genuine relative cofibration condition. The source-to-middle arrow of
that zero object is an isomorphism between zero objects. Its pushout corner
is the target source, and the corner map is the target cofiber inclusion.

Zero morphisms are derived only inside the proof to use the existing
evaluation zero-object API. The theorem has the original general Waldhausen
hypotheses and exports no additional dictionary or Waldhausen structure.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

private theorem relativeOfZeroSource
    {A B : Waldhausen.CofibrationArrow C} (f : A ⟶ B)
    (hL : IsZero A.left) (hR : IsZero A.right) :
    Waldhausen.IsRelativeCofibration C f := by
  let e : A.left ≅ (0 : C) := hL.isoZero
  have hzero : IsCofibration (e.inv ≫ f.left) :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
  have hLeft : IsCofibration f.left := by
    have hPre := MorphismProperty.RespectsIso.precomp
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) e.hom _ hzero
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hPre
  let inB : A.right ⟶ B.left := hR.to_ B.left
  have hHom : A.hom = (hL.iso hR).hom := hL.eq_of_src _ _
  let : IsIso A.hom := by
    rw [hHom]
    infer_instance
  have hPushout : IsPushout A.hom f.left inB (𝟙 B.left) :=
    IsPushout.of_horiz_isIso ⟨hL.eq_of_src _ _⟩
  refine ⟨hLeft, B.left, inB, 𝟙 B.left, B.hom, hPushout, ?_, ?_, B.prop⟩
  · exact hR.eq_of_src _ _
  · exact Category.id_comp _

/-- Every map out of the existing cofiber-category zero object satisfies
the genuine relative cofibration condition. -/
theorem zero_outOf_isRelativeCofibration
    (X : CofiberSequenceCategory C) (f : (0 : CofiberSequenceCategory C) ⟶ X) :
    relativeCofibrations C f := by
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  have hSource : IsZero ((source C).obj (0 : CofiberSequenceCategory C)) :=
    (((evaluation (Fin 3) C).obj ⟨0, by decide⟩).map_isZero
      ((forget C).map_isZero (isZero_zero (CofiberSequenceCategory C))))
  have hMiddle : IsZero ((middle C).obj (0 : CofiberSequenceCategory C)) :=
    (((evaluation (Fin 3) C).obj ⟨1, by decide⟩).map_isZero
      ((forget C).map_isZero (isZero_zero (CofiberSequenceCategory C))))
  apply (mem_relativeCofibrations_iff C f).mpr
  apply relativeOfZeroSource C ((sourceMiddleArrow C).map f)
  · have hObj := congrArg
      (fun F : CofiberSequenceCategory C ⥤ C => F.obj (0 : CofiberSequenceCategory C))
      (sourceMiddleArrow_source C)
    change ((sourceMiddleArrow C).obj (0 : CofiberSequenceCategory C)).left =
      (source C).obj (0 : CofiberSequenceCategory C) at hObj
    rw [hObj]
    exact hSource
  · have hObj := congrArg
      (fun F : CofiberSequenceCategory C ⥤ C => F.obj (0 : CofiberSequenceCategory C))
      (sourceMiddleArrow_middle C)
    change ((sourceMiddleArrow C).obj (0 : CofiberSequenceCategory C)).right =
      (middle C).obj (0 : CofiberSequenceCategory C) at hObj
    rw [hObj]
    exact hMiddle

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
