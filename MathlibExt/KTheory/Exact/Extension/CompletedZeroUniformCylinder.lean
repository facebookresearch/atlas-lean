/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroUniformBaseIso
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# The original uniform mapped-zero cylinder classifier

The SAME projected total-source comparison is the original constant
mapped-zero Iso. Its cylinder functor factors through the original interval
arrow in both directions. Actual underlying zero objects determine its
Quillen arrows; no completed-Core morphisms or components are identified.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory CategoryTheory.Prod

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uA vA uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualQZeroArrowHEq
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B A' B' : QuillenQ D} (ha : A = A') (hb : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hB : IsZero B'.obj) : HEq f g := by
  cases ha
  cases hb
  rcases A with ⟨A⟩
  rcases B with ⟨B⟩
  exact heq_of_eq (QuillenQ.hom_eq_of_target_isZero f g hB)

private theorem actualConstantClassifierObject
    {T : Type uA} [Category.{vA} T]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (h : A ⟶ B) (x : T) (i : Fin 2) :
    (NatTrans.nerveCylinderFunctor ((Functor.const T).map h)).obj (x, i) =
      (CategoryTheory.Prod.snd T (Fin 2) ⋙ ComposableArrows.mk₁ h).obj (x, i) := by
  fin_cases i
  · exact NatTrans.nerveCylinderFunctor_obj_zero ((Functor.const T).map h) x
  · exact NatTrans.nerveCylinderFunctor_obj_one ((Functor.const T).map h) x

private theorem actualZeroConstantClassifier
    {T : Type uA} [Category.{vA} T]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (h : A ⟶ B) (hA : IsZero A.obj) (hB : IsZero B.obj) :
    NatTrans.nerveCylinderFunctor ((Functor.const T).map h) =
      CategoryTheory.Prod.snd T (Fin 2) ⋙ ComposableArrows.mk₁ h := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · rintro ⟨x, i⟩
    exact actualConstantClassifierObject h x i
  · rintro ⟨x, i⟩ ⟨y, j⟩ f
    have hTarget : IsZero
        ((CategoryTheory.Prod.snd T (Fin 2) ⋙ ComposableArrows.mk₁ h).obj (y, j)).obj := by
      fin_cases j
      · exact hA
      · exact hB
    exact actualQZeroArrowHEq
      (actualConstantClassifierObject h x i) (actualConstantClassifierObject h y j)
      ((NatTrans.nerveCylinderFunctor ((Functor.const T).map h)).map f)
      ((CategoryTheory.Prod.snd T (Fin 2) ⋙ ComposableArrows.mk₁ h).map f) hTarget

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualUniformForwardCylinder :
    NatTrans.nerveCylinderFunctor (completedZeroUniformBaseIso F).hom =
      CategoryTheory.Prod.snd (SInverse (Core C) (Core C)) (Fin 2) ⋙
        ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).hom := by
  have hWhole := congrArg (fun e => NatTrans.nerveCylinderFunctor e.hom)
    (completedZeroUniformBaseIso_value F)
  have hMappedZero : IsZero ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)).obj :=
    (isZero_zero D).of_iso F.mapZeroObject
  exact hWhole.trans (actualZeroConstantClassifier
    (T := SInverse (Core C) (Core C)) (QuillenQ.zeroComparisonIso F).hom
    hMappedZero (isZero_zero D))

/-- The SAME original forward base comparison's whole cylinder factors through its canonical zero
  edge. -/
public theorem completedZeroUniformBaseCylinder_forward :
    NatTrans.nerveCylinderFunctor (completedZeroUniformBaseIso F).hom =
      CategoryTheory.Prod.snd (SInverse (Core C) (Core C)) (Fin 2) ⋙
        ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).hom :=
  actualUniformForwardCylinder F

private theorem actualUniformInverseCylinder :
    NatTrans.nerveCylinderFunctor (completedZeroUniformBaseIso F).inv =
      CategoryTheory.Prod.snd (SInverse (Core C) (Core C)) (Fin 2) ⋙
        ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).inv := by
  have hWhole := congrArg (fun e => NatTrans.nerveCylinderFunctor e.inv)
    (completedZeroUniformBaseIso_value F)
  have hMappedZero : IsZero ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)).obj :=
    (isZero_zero D).of_iso F.mapZeroObject
  exact hWhole.trans (actualZeroConstantClassifier
    (T := SInverse (Core C) (Core C)) (QuillenQ.zeroComparisonIso F).inv
    (isZero_zero D) hMappedZero)

/-- The SAME original inverse comparison's whole cylinder keeps the canonical inverse zero edge. -/
public theorem completedZeroUniformBaseCylinder_inverse :
    NatTrans.nerveCylinderFunctor (completedZeroUniformBaseIso F).inv =
      CategoryTheory.Prod.snd (SInverse (Core C) (Core C)) (Fin 2) ⋙
        ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).inv :=
  actualUniformInverseCylinder F

end AlgebraicKTheory.FixedTargetExtension

end
