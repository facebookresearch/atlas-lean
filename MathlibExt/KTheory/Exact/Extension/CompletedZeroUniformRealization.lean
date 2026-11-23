/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroUniformCylinder
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.CategoryTheory.NerveHomotopyRealization

/-!
# Every-point uniformity of the original mapped-zero realized cylinder

The actual original lifted constant comparison retains both original
category lift charts. Its classifier factors through the same interval
arrow by the original Q-zero span theorem after the actual inverse lift.
The proper original cylinder-chain and homotopy-field values transfer this
to the whole simplicial cylinder and its realized family. Both original
projected comparison directions are uniform over EVERY original point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory CategoryTheory.Prod ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] CategoryTheory.uliftCategory

universe uT vT uC vC uD vD uNative wQ

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualQArrowsToZeroEq
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (f g : A ⟶ B) (hB : IsZero B.obj) : f = g := by
  rcases A with ⟨A⟩
  rcases B with ⟨B⟩
  exact QuillenQ.hom_eq_of_target_isZero f g hB

private theorem actualLiftedQArrowHEq
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B A' B' : ULiftHom.{wQ}
      (ULift.{wQ} (QuillenQ D))}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (hZero : IsZero
      (((ULiftHomULiftCategory.equiv.{wQ, wQ,
        max uD vD, uD} (QuillenQ D)).inverse.obj B').obj)) : HEq f g := by
  cases hA
  cases hB
  apply heq_of_eq
  let U := ULiftHomULiftCategory.equiv.{wQ, wQ,
    max uD vD, uD} (QuillenQ D)
  exact U.inverse.map_injective (actualQArrowsToZeroEq (U.inverse.map f) (U.inverse.map g) hZero)

private theorem actualNativeZeroClassifier
    {T : Type uT} [Category.{vT} T]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (h : A ⟶ B) (hA : IsZero A.obj) (hB : IsZero B.obj) :
    let UC := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD, vT, uT} T
    let UD := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD,
      max uD vD, uD} (QuillenQ D)
    NatTrans.nerveCylinderFunctor
        (Functor.whiskerLeft UC.inverse (Functor.whiskerRight ((Functor.const T).map h) UD.functor))
            =
      CategoryTheory.Prod.snd (ULiftHom.{max uT vT uD vD}
        (ULift.{max uT vT uD vD} T)) (Fin 2) ⋙ ComposableArrows.mk₁ (UD.functor.map h) := by
  let UC := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD, vT, uT} T
  let UD := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD,
    max uD vD, uD} (QuillenQ D)
  let alpha := Functor.whiskerLeft UC.inverse
    (Functor.whiskerRight ((Functor.const T).map h) UD.functor)
  let R := CategoryTheory.Prod.snd (ULiftHom.{max uT vT uD vD}
    (ULift.{max uT vT uD vD} T)) (Fin 2) ⋙ ComposableArrows.mk₁ (UD.functor.map h)
  have hObject (x : ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} T))
      (i : Fin 2) : (NatTrans.nerveCylinderFunctor alpha).obj (x, i) = R.obj (x, i) := by
    fin_cases i
    · exact NatTrans.nerveCylinderFunctor_obj_zero alpha x
    · exact NatTrans.nerveCylinderFunctor_obj_one alpha x
  refine CategoryTheory.Functor.hext (fun x => hObject x.1 x.2) ?_
  rintro ⟨x, i⟩ ⟨y, j⟩ f
  have hZero : IsZero ((UD.inverse.obj (R.obj (y, j))).obj) := by
    fin_cases j
    · exact hA
    · exact hB
  exact actualLiftedQArrowHEq (hObject x i) (hObject y j)
    ((NatTrans.nerveCylinderFunctor alpha).map f) (R.map f) hZero

private theorem actualSimplicialCylinderFromClassifier
    {X Y : Type uNative} [Category.{uNative} X] [Category.{uNative} Y]
    {F G : X ⥤ Y} (alpha : F ⟶ G) {A B : Y} (h : A ⟶ B)
    (hClassifier : NatTrans.nerveCylinderFunctor alpha =
      CategoryTheory.Prod.snd X (Fin 2) ⋙ ComposableArrows.mk₁ h) :
    NatTrans.nerveHomotopyMap alpha =
      CartesianMonoidalCategory.snd (nerve X) (Δ[1] : SSet.{uNative}) ≫
        SSet.yonedaEquiv.symm ((nerve.edgeMk h).edge) := by
  ext Delta x
  have hWhole := NatTrans.nerveHomotopyMap_app_value alpha Delta x
  have hData := congrArg (fun K : X × Fin 2 ⥤ Y =>
    (K.mapComposableArrows Delta.unop.len).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)) hClassifier
  exact hWhole.trans (hData.trans (by rfl))

private theorem actualProductInverseFirst
    {X Y : TopCat.{uNative}} (x : X) (y : Y) :
    (Limits.prod.fst : X ⨯ Y ⟶ X) ((TopCat.prodIsoProd X Y).inv (x, y)) = x :=
  (TopCat.comp_app (TopCat.prodIsoProd X Y).inv (Limits.prod.fst : X ⨯ Y ⟶ X) (x, y)).symm.trans
    (ConcreteCategory.congr_hom (TopCat.prodIsoProd_inv_fst X Y) (x, y))

private theorem actualNativeZeroRealizationUniform
    {T : Type uT} [Category.{vT} T]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (h : A ⟶ B) (hA : IsZero A.obj) (hB : IsZero B.obj)
    (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (ULiftHom.{max uT vT uD vD}
      (ULift.{max uT vT uD vD} T)))) :
    let UC := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD, vT, uT} T
    let UD := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD,
      max uD vD, uD} (QuillenQ D)
    let LF := UC.inverse ⋙ (Functor.const T).obj A ⋙ UD.functor
    let LG := UC.inverse ⋙ (Functor.const T).obj B ⋙ UD.functor
    let alpha : LF ⟶ LG := Functor.whiskerLeft UC.inverse
      (Functor.whiskerRight ((Functor.const T).map h) UD.functor)
    SSet.realizeHomotopy
        (nerve (ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} T)))
        (nerve (ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} (QuillenQ D))))
        (nerveMap LF) (nerveMap LG) (NatTrans.nerveHomotopy alpha) (t, x) =
      SSet.realizeHomotopy
        (nerve (ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} T)))
        (nerve (ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} (QuillenQ D))))
        (nerveMap LF) (nerveMap LG) (NatTrans.nerveHomotopy alpha) (t, y) := by
  let UC := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD, vT, uT} T
  let UD := ULiftHomULiftCategory.equiv.{max uT vT uD vD, max uT vT uD vD,
    max uD vD, uD} (QuillenQ D)
  let LX := ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} T)
  let LY := ULiftHom.{max uT vT uD vD} (ULift.{max uT vT uD vD} (QuillenQ D))
  let F := UC.inverse ⋙ (Functor.const T).obj A ⋙ UD.functor
  let G := UC.inverse ⋙ (Functor.const T).obj B ⋙ UD.functor
  let alpha : F ⟶ G := Functor.whiskerLeft UC.inverse
    (Functor.whiskerRight ((Functor.const T).map h) UD.functor)
  let H := NatTrans.nerveHomotopy alpha
  let q := SSet.yonedaEquiv.symm ((nerve.edgeMk (UD.functor.map h)).edge)
  have hCylinder : H.h = CartesianMonoidalCategory.snd (nerve LX)
      (Δ[1] : SSet.{max uT vT uD vD}) ≫ q :=
    (NatTrans.nerveHomotopy_h_value alpha).trans
      (actualSimplicialCylinderFromClassifier alpha (UD.functor.map h)
        (actualNativeZeroClassifier h hA hB))
  have hFactor := SSet.realizeHomotopyMap_interval_factor H q hCylinder
  change SSet.realizeHomotopyMap (nerve LX) (nerve LY) (nerveMap F) (nerveMap G) H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve LX))).inv
        (TopCat.I.homeomorph.symm t, x)) =
    SSet.realizeHomotopyMap (nerve LX) (nerve LY) (nerveMap F) (nerveMap G) H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve LX))).inv
        (TopCat.I.homeomorph.symm t, y))
  rw [hFactor]
  simp only [TopCat.comp_app]
  exact congrArg (fun s => SSet.toTop.map q (SSet.stdSimplex.toTopObjIsoI.inv s))
    ((actualProductInverseFirst (TopCat.I.homeomorph.symm t) x).trans
      (actualProductInverseFirst (TopCat.I.homeomorph.symm t) y).symm)

private theorem actualMixedConstantZeroHomotopyUniform
    {T : Type uT} [Category.{vT} T]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {A B : QuillenQ D} (h : A ⟶ B) (hA : IsZero A.obj) (hB : IsZero B.obj)
    (t : unitInterval) (x y : SSet.toTop.obj (nerve T)) :
    realizedNerveFunctorMapHomotopy ((Functor.const T).map h) (t, x) =
      realizedNerveFunctorMapHomotopy ((Functor.const T).map h) (t, y) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uT, vT, max uT vT uD vD} T
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, max uD vD, max uT vT uD vD} (QuillenQ D)
  have hx := realizedNerveFunctorMapHomotopy_value ((Functor.const T).map h) t x
  have hy := realizedNerveFunctorMapHomotopy_value ((Functor.const T).map h) t y
  have hNative := actualNativeZeroRealizationUniform h hA hB t (HC.symm x) (HC.symm y)
  exact hx.trans ((congrArg HD hNative).trans hy.symm)

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualOriginalForwardUniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, y) := by
  let T := SInverse (Core C) (Core C)
  let A := (QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)
  let B := (⟨(0 : D)⟩ : QuillenQ D)
  have hAlpha : (completedZeroUniformBaseIso F).hom =
      (Functor.const T).map (QuillenQ.zeroComparisonIso F).hom :=
    congrArg Iso.hom (completedZeroUniformBaseIso_value F)
  have hA : IsZero A.obj := (isZero_zero D).of_iso F.mapZeroObject
  have hB : IsZero B.obj := isZero_zero D
  have hL := congrArg (fun alpha => realizedNerveFunctorMapHomotopy alpha (t, x)) hAlpha
  have hR := congrArg (fun alpha => realizedNerveFunctorMapHomotopy alpha (t, y)) hAlpha
  exact hL.trans ((actualMixedConstantZeroHomotopyUniform
    (QuillenQ.zeroComparisonIso F).hom hA hB t x y).trans hR.symm)

/-- EVERY original point has the SAME forward interval value in the actual projected total-source
  family. -/
public theorem completedZeroUniformBaseHomotopy_forward_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, y) :=
  actualOriginalForwardUniform F t x y

private theorem actualOriginalInverseUniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, y) := by
  let T := SInverse (Core C) (Core C)
  let A := (QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)
  let B := (⟨(0 : D)⟩ : QuillenQ D)
  have hAlpha : (completedZeroUniformBaseIso F).inv =
      (Functor.const T).map (QuillenQ.zeroComparisonIso F).inv :=
    congrArg Iso.inv (completedZeroUniformBaseIso_value F)
  have hA : IsZero A.obj := (isZero_zero D).of_iso F.mapZeroObject
  have hB : IsZero B.obj := isZero_zero D
  have hL := congrArg (fun alpha => realizedNerveFunctorMapHomotopy alpha (t, x)) hAlpha
  have hR := congrArg (fun alpha => realizedNerveFunctorMapHomotopy alpha (t, y)) hAlpha
  exact hL.trans ((actualMixedConstantZeroHomotopyUniform
    (QuillenQ.zeroComparisonIso F).inv hB hA t x y).trans hR.symm)

/-- EVERY original point retains the SAME inverse interval value in the original inverse family. -/
public theorem completedZeroUniformBaseHomotopy_inverse_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, y) :=
  actualOriginalInverseUniform F t x y

end AlgebraicKTheory.FixedTargetExtension

end
