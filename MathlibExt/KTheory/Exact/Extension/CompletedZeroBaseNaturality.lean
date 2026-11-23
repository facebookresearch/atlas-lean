/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroTotalNaturality
public import MathlibExt.KTheory.Exact.Quillen.TargetZero
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence

/-!
# Whole original completed-zero base functors and scalar component edges

The actual strict-fiber equality determines the base on every completed
pair. Original stabilized-functor target naturality gives the actual
mapped-zero base. The original total-source components project to the
canonical mapped-zero Iso in both directions. The Quillen span theorem
is used only for arrows into an actual underlying zero object; it makes
no equality assertion about localized extension or completed-Core arrows.
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

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualQArrowHEqAtZero
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B A' B' : QuillenQ D} (ha : A = A') (hb : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hB : IsZero B'.obj) : HEq f g := by
  cases ha
  cases hb
  rcases A with ⟨A⟩
  rcases B with ⟨B⟩
  exact heq_of_eq (QuillenQ.hom_eq_of_target_isZero f g hB)

private theorem actualCompletedZeroBaseObject
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SInverse (Core C) (Core C)) :
    (ExtensionCategory.localizedTarget (C := C)).obj
      ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).obj a) =
        (⟨(0 : C)⟩ : QuillenQ C) := by
  let z := (localizedFiberFunctor (0 : C)).obj ((zeroLocalizedFunctor (C := C)).obj a)
  have hObject : z.val = (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).obj a :=
    Functor.congr_obj (localizedFiberFunctor_forget (C := C) (X := (0 : C)))
      ((zeroLocalizedFunctor (C := C)).obj a)
  exact (congrArg (ExtensionCategory.localizedTarget (C := C)).obj hObject.symm).trans z.property

private theorem actualCompletedZeroWholeBase
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.localizedTarget (C := C) =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : C)⟩ : QuillenQ C) := by
  refine Functor.hext (actualCompletedZeroBaseObject (C := C)) ?_
  intro a b f
  exact actualQArrowHEqAtZero (actualCompletedZeroBaseObject a) (actualCompletedZeroBaseObject b)
    ((ExtensionCategory.localizedTarget (C := C)).map
      ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).map f))
    (𝟙 (⟨(0 : C)⟩ : QuillenQ C)) (isZero_zero C)

/-- The ACTUAL whole base functor is the chosen Q-zero on every completed pair and arrow. -/
public theorem completedZeroTotalBase_eq_const
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.localizedTarget (C := C) =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : C)⟩ : QuillenQ C) :=
  actualCompletedZeroWholeBase (C := C)

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualMappedZeroBaseObject (a : SInverse (Core C) (Core C)) :
    (ExtensionCategory.localizedTarget (C := D)).obj
        ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
          ExtensionCategory.stabilizedFunctorMap F).obj a) =
      (QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C) :=
  (Functor.congr_obj (ExtensionCategory.stabilizedFunctorMap_target F)
    ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).obj a)).trans
      (congrArg (QuillenQ.map F).obj (actualCompletedZeroBaseObject a))

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetZeroBaseObject (a : SInverse (Core C) (Core C)) :
    (ExtensionCategory.localizedTarget (C := D)).obj
        ((completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj a) =
      (⟨(0 : D)⟩ : QuillenQ D) :=
  actualCompletedZeroBaseObject ((completedCoreFunctor F).obj a)

private theorem actualMappedZeroWholeBase :
    zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F ⋙ ExtensionCategory.localizedTarget (C := D) =
      (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) := by
  refine Functor.hext (actualMappedZeroBaseObject F) ?_
  intro a b f
  have hZero : IsZero ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)).obj :=
    (isZero_zero D).of_iso F.mapZeroObject
  exact actualQArrowHEqAtZero (actualMappedZeroBaseObject F a) (actualMappedZeroBaseObject F b)
    ((ExtensionCategory.localizedTarget (C := D)).map
      ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).map f))
    (𝟙 ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C))) hZero

/-- The original stabilized scalar map has its ACTUAL constant mapped-zero base on all components.
-/
public theorem completedZeroMappedTotalBase_eq_const :
    zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F ⋙ ExtensionCategory.localizedTarget (C := D) =
      (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) :=
  actualMappedZeroWholeBase F

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetZeroWholeBase :
    completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D) ⋙
        ExtensionCategory.localizedTarget (C := D) =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) := by
  refine Functor.hext (actualTargetZeroBaseObject F) ?_
  intro a b f
  exact actualQArrowHEqAtZero (actualTargetZeroBaseObject F a) (actualTargetZeroBaseObject F b)
    ((ExtensionCategory.localizedTarget (C := D)).map
      ((completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).map f))
    (𝟙 (⟨(0 : D)⟩ : QuillenQ D)) (isZero_zero D)

omit [ExactCategory C] [F.IsExact] in
/-- The SAME target Core/zero map keeps the chosen zero base on every completed component. -/
public theorem completedZeroTargetTotalBase_eq_const :
    completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D) ⋙
        ExtensionCategory.localizedTarget (C := D) =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) :=
  actualTargetZeroWholeBase F

private theorem actualTotalSourceHomZeroEdge (a : SInverse (Core C) (Core C)) :
    HEq ((ExtensionCategory.localizedTarget (C := D)).map
      (completedZeroTotalSourceComponent F a).hom) (QuillenQ.zeroComparisonIso F).hom :=
  actualQArrowHEqAtZero (actualMappedZeroBaseObject F a) (actualTargetZeroBaseObject F a)
    ((ExtensionCategory.localizedTarget (C := D)).map (completedZeroTotalSourceComponent F a).hom)
    (QuillenQ.zeroComparisonIso F).hom (isZero_zero D)

/-- Every original forward total-source component projects to the SAME canonical mapped-zero Iso. -/
public theorem completedZeroTotalSourceComponent_target_hom_heq (a : SInverse (Core C) (Core C)) :
    HEq ((ExtensionCategory.localizedTarget (C := D)).map
      (completedZeroTotalSourceComponent F a).hom) (QuillenQ.zeroComparisonIso F).hom :=
  actualTotalSourceHomZeroEdge F a

private theorem actualTotalSourceInvZeroEdge (a : SInverse (Core C) (Core C)) :
    HEq ((ExtensionCategory.localizedTarget (C := D)).map
      (completedZeroTotalSourceComponent F a).inv) (QuillenQ.zeroComparisonIso F).inv := by
  have hZero : IsZero ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)).obj :=
    (isZero_zero D).of_iso F.mapZeroObject
  exact actualQArrowHEqAtZero (actualTargetZeroBaseObject F a) (actualMappedZeroBaseObject F a)
    ((ExtensionCategory.localizedTarget (C := D)).map (completedZeroTotalSourceComponent F a).inv)
    (QuillenQ.zeroComparisonIso F).inv hZero

/-- Every SAME inverse total-source component projects to the original inverse mapped-zero Iso. -/
public theorem completedZeroTotalSourceComponent_target_inv_heq (a : SInverse (Core C) (Core C)) :
    HEq ((ExtensionCategory.localizedTarget (C := D)).map
      (completedZeroTotalSourceComponent F a).inv) (QuillenQ.zeroComparisonIso F).inv :=
  actualTotalSourceInvZeroEdge F a

end AlgebraicKTheory.FixedTargetExtension

end
