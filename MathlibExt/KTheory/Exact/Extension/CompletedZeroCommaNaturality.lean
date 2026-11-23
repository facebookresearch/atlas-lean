/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroTotalNaturality
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroCommaFunctorMap
public import MathlibExt.KTheory.Exact.Quillen.TargetZero
public import MathlibExt.CategoryTheory.FiberedCategory.FiberToStructuredArrow
public import Mathlib.CategoryTheory.Whiskering

/-!
# Actual original completed-zero comma naturality

The original strict-fiber projection and zero-comma map project to the
actual total functors. The internally derived original total NatIso lifts
to the same comma objects and maps. Its comma triangle is proved by the
original Quillen span theorem for arrows into the actual underlying zero
quotient, determined by the stored fiber equality. No localized arrow is
equalized from a middle coordinate or a connected-component label.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem actualQArrowsToZeroEqual
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {X Z : QuillenQ D} (f g : X ⟶ Z) (hZ : IsZero Z.obj) : f = g := by
  rcases X with ⟨X⟩
  rcases Z with ⟨Z⟩
  exact QuillenQ.hom_eq_of_target_isZero f g hZ

private def actualCompletedZeroCommaProjectionIso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      StructuredArrow.proj (⟨(0 : C)⟩ : QuillenQ C)
        (ExtensionCategory.localizedTarget (C := C)) ≅
    FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
      FixedTargetExtension.localizedForget (0 : C) := by
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := C)
  let Y := FixedTargetExtension.localizedFiberFunctor (0 : C)
  let U := Functor.fiberToStructuredArrow
    (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)
  let P := StructuredArrow.proj (⟨(0 : C)⟩ : QuillenQ C)
    (ExtensionCategory.localizedTarget (C := C))
  let I := FixedTargetExtension.localizedFiberForget (0 : C)
  let hU : U ⋙ P ≅ I := eqToIso (Functor.fiberToStructuredArrow_projection
    (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C))
  let hY : Y ⋙ I ≅ FixedTargetExtension.localizedForget (0 : C) :=
    eqToIso (FixedTargetExtension.localizedFiberFunctor_forget (C := C) (X := (0 : C)))
  exact Functor.associator Z (Y ⋙ U) P ≪≫
    Functor.isoWhiskerLeft Z (Functor.associator Y U P) ≪≫
    Functor.isoWhiskerLeft Z (Functor.isoWhiskerLeft Y hU) ≪≫
    Functor.isoWhiskerLeft Z hY

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private def actualCompletedZeroCommaProjectedNatIso :
    ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      zeroStructuredArrowMap F) ⋙
      StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) ≅
    (completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)) ⋙
      StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) := by
  let LC := FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)
  let LD := FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  let PC := StructuredArrow.proj (⟨(0 : C)⟩ : QuillenQ C)
    (ExtensionCategory.localizedTarget (C := C))
  let PD := StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
    (ExtensionCategory.localizedTarget (C := D))
  let M := zeroStructuredArrowMap F
  let H := ExtensionCategory.stabilizedFunctorMap F
  let K := completedCoreFunctor F
  let ZC := FixedTargetExtension.zeroLocalizedFunctor (C := C)
  let YC := FixedTargetExtension.localizedForget (0 : C)
  let eL : (LC ⋙ M) ⋙ PD ≅ ZC ⋙ YC ⋙ H :=
    Functor.associator LC M PD ≪≫
      Functor.isoWhiskerLeft LC (eqToIso (zeroStructuredArrowMap_projection F)) ≪≫
      (Functor.associator LC PC H).symm ≪≫
      Functor.isoWhiskerRight (actualCompletedZeroCommaProjectionIso (C := C)) H ≪≫
      Functor.associator ZC YC H
  let eR : (K ⋙ LD) ⋙ PD ≅ K ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
      FixedTargetExtension.localizedForget (0 : D) :=
    Functor.associator K LD PD ≪≫
      Functor.isoWhiskerLeft K (actualCompletedZeroCommaProjectionIso (C := D))
  exact eL ≪≫ FixedTargetExtension.completedZeroTotalNaturalityIso F ≪≫ eR.symm

/-- The original projected comma functors have the internally derived total-source NatIso. -/
public def completedZeroCommaProjectedNaturalityIso :
    ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      zeroStructuredArrowMap F) ⋙
      StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) ≅
    (completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)) ⋙
      StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) :=
  actualCompletedZeroCommaProjectedNatIso F

private def actualCompletedZeroCommaNatIso :
    (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      zeroStructuredArrowMap F ≅
    completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
      FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
      Functor.fiberToStructuredArrow
        (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D) := by
  let L := (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
    zeroStructuredArrowMap F
  let R := completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  let P := StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
    (ExtensionCategory.localizedTarget (C := D))
  let E : L ⋙ P ≅ R ⋙ P := completedZeroCommaProjectedNaturalityIso F
  let c (a : SInverse (Core C) (Core C)) : L.obj a ≅ R.obj a :=
    StructuredArrow.isoMk (E.app a) (by
      let z := (FixedTargetExtension.localizedFiberFunctor (0 : D)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := D)).obj ((completedCoreFunctor F).obj a))
      have hRight : (R.obj a).right = z.val := Functor.fiberToStructuredArrow_obj_right
        (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D) z
      have hQuotient : (ExtensionCategory.localizedTarget (C := D)).obj (R.obj a).right =
          (⟨(0 : D)⟩ : QuillenQ D) :=
        (congrArg (ExtensionCategory.localizedTarget (C := D)).obj hRight).trans z.property
      have hUnderlying :
          ((ExtensionCategory.localizedTarget (C := D)).obj (R.obj a).right).obj = (0 : D) :=
        congrArg (fun Q : QuillenQ D => Q.obj) hQuotient
      have hZero : IsZero
          ((ExtensionCategory.localizedTarget (C := D)).obj (R.obj a).right).obj :=
        hUnderlying.symm ▸ isZero_zero D
      exact actualQArrowsToZeroEqual _ _ hZero)
  refine NatIso.ofComponents c ?_
  intro a b f
  apply StructuredArrow.hom_ext
  change (L.map f).right ≫ (E.app b).hom = (E.app a).hom ≫ (R.map f).right
  exact E.hom.naturality f

/-- The SAME original completed-zero comma functors are naturally isomorphic on every object and
  arrow. -/
public def completedZeroCommaNaturalityIso :
    (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      zeroStructuredArrowMap F ≅
    completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
      FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
      Functor.fiberToStructuredArrow
        (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D) :=
  actualCompletedZeroCommaNatIso F

private theorem actualCommaHomRightValue (a : SInverse (Core C) (Core C)) :
    ((completedZeroCommaNaturalityIso F).app a).hom.right =
      ((completedZeroCommaProjectedNaturalityIso F).app a).hom := rfl

/-- Its forward right component is the actual projected original total-source component. -/
public theorem completedZeroCommaNaturalityIso_hom_right (a : SInverse (Core C) (Core C)) :
    ((completedZeroCommaNaturalityIso F).app a).hom.right =
      ((completedZeroCommaProjectedNaturalityIso F).app a).hom :=
  actualCommaHomRightValue F a

private theorem actualCommaInvRightValue (a : SInverse (Core C) (Core C)) :
    ((completedZeroCommaNaturalityIso F).app a).inv.right =
      ((completedZeroCommaProjectedNaturalityIso F).app a).inv := rfl

/-- Its inverse right component retains the SAME inverse original total-source component. -/
public theorem completedZeroCommaNaturalityIso_inv_right (a : SInverse (Core C) (Core C)) :
    ((completedZeroCommaNaturalityIso F).app a).inv.right =
      ((completedZeroCommaProjectedNaturalityIso F).app a).inv :=
  actualCommaInvRightValue F a

end AlgebraicKTheory.OriginalQZeroComparison

end
