/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroIdentityRowImage
public import MathlibExt.KTheory.Exact.Extension.RowIsoDiagram
public import MathlibExt.Algebra.Homology.ShortComplex.HEqTransport

/-!
# The actual identity-coordinate zero-row source Iso

The original given zero row maps through the actual extension functor.
Its public whole-row image views transport the canonical identity-row
Iso to those exact source/target object presentations. First and middle
components stay identity, and the given quotient uses mapZeroObject.
No source Iso, component identity or comparison outcome is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalZeroGivenRowViews (A : Core C) :
    ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
      AlgebraicKTheory.ExtensionCategory.mapFunctor F).obj A).row =
        (zeroRow A).toExtension.row.map F ∧
      ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj A).row =
        (zeroRow (F.core.obj A)).toExtension.row := by
  let ZC := zeroRowFunctor (C := C)
  let YC := givenRowFunctor (C := C) (0 : C)
  let G := AlgebraicKTheory.ExtensionCategory.mapFunctor F
  let ZD := zeroRowFunctor (C := D)
  let YD := givenRowFunctor (C := D) (0 : D)
  have hz : ZC.obj A = zeroRow A := rfl
  have hGiven : YC.obj (ZC.obj A) = (zeroRow A).toExtension :=
    (givenRowFunctor_obj (ZC.obj A)).trans
      (congrArg (fun E : FixedTargetExtension C (0 : C) => E.toExtension) hz)
  have hs : (G.obj (YC.obj (ZC.obj A))).row = (zeroRow A).toExtension.row.map F :=
    (congrArg (fun E : AlgebraicKTheory.ExtensionCategory D => E.row)
      (AlgebraicKTheory.ExtensionCategory.mapFunctor_obj F (YC.obj (ZC.obj A)))).trans
      ((AlgebraicKTheory.ExtensionCategory.mapObject_row F (YC.obj (ZC.obj A))).trans
        (congrArg (fun E : AlgebraicKTheory.ExtensionCategory C => E.row.map F) hGiven))
  have hd : ZD.obj (F.core.obj A) = zeroRow (F.core.obj A) := rfl
  have ht : (YD.obj (ZD.obj (F.core.obj A))).row =
      (zeroRow (F.core.obj A)).toExtension.row :=
    (congrArg (fun E : AlgebraicKTheory.ExtensionCategory D => E.row)
      (givenRowFunctor_obj (ZD.obj (F.core.obj A)))).trans
      (congrArg (fun E : FixedTargetExtension D (0 : D) => E.toExtension.row) hd)
  exact ⟨hs, ht⟩


private def originalZeroGivenRowCoordinateIso (A : Core C) :
    ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
      AlgebraicKTheory.ExtensionCategory.mapFunctor F).obj A).row ≅
      ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj A).row :=
  eqToIso (originalZeroGivenRowViews F A).1 ≪≫ mapZeroIdentityRowIso F A ≪≫
    (eqToIso (originalZeroGivenRowViews F A).2).symm

/-- The actual zero-row image Iso is built with identity object coordinates. -/
public def zeroRowIdentityCoordinateIso (A : Core C) :
    (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
      AlgebraicKTheory.ExtensionCategory.mapFunctor F).obj A ≅
      (F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj A :=
  AlgebraicKTheory.ExtensionCategory.isoOfRowIso (originalZeroGivenRowCoordinateIso F A)


private theorem originalZeroCoordinateMiddleComputed (A : Core C) :
    HEq (AlgebraicKTheory.ExtensionCategory.homNormalization
      (zeroRowIdentityCoordinateIso F A).hom).hom.2.hom (𝟙 (F.obj A.of)) := by
  let r := originalZeroGivenRowCoordinateIso F A
  let t := mapZeroIdentityRowIso F A
  let d := ExtensionDiagram.ofRowIso r
  have hs := (originalZeroGivenRowViews F A).1
  have ht := (originalZeroGivenRowViews F A).2
  have hRow : HEq r.hom t.hom := (conj_eqToHom_iff_heq _ _ hs ht).1 rfl
  have hComponent := ShortComplex.Hom.components_heq_of_rows_eq hs ht hRow
  have hIdentity : HEq r.hom.τ₂ (𝟙 (F.obj A.of)) :=
    hComponent.2.1.trans (mapZeroIdentityRowIso_components F A).2.1
  have hMiddle : (AlgebraicKTheory.ExtensionCategory.homNormalization
      (zeroRowIdentityCoordinateIso F A).hom).hom.2.hom = d.beta :=
    (congrArg (fun f :
        (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          AlgebraicKTheory.ExtensionCategory.mapFunctor F).obj A ⟶
        (F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj A =>
      (AlgebraicKTheory.ExtensionCategory.homNormalization f).hom.2.hom)
        (AlgebraicKTheory.ExtensionCategory.isoOfRowIso_hom r)).trans (by rfl)
  exact (heq_of_eq hMiddle).trans
    ((heq_of_eq (ExtensionDiagram.ofRowIso_components r).2.1).trans hIdentity)

/-- The actual source component retains the literal identity on the image middle object. -/
public theorem zeroRowIdentityCoordinateIso_middle_heq (A : Core C) :
    HEq (AlgebraicKTheory.ExtensionCategory.homNormalization
      (zeroRowIdentityCoordinateIso F A).hom).hom.2.hom (𝟙 (F.obj A.of)) :=
  originalZeroCoordinateMiddleComputed F A

end AlgebraicKTheory.FixedTargetExtension

end
