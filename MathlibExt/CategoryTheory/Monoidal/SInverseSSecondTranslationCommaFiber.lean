/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomology
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationComma
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiberCoreTransport

/-!
# Second translation from right-comma categories to strict fibers

Second-coordinate translation commutes with the right-comma-to-fiber
comparison up to a canonical natural transformation.  Its component is the
unique vertical factor of the translated chosen cocartesian lift through the
chosen lift of the translated comma object.

Applying category homology and then the core/fiber comparison identifies the
resulting right-comma homology endomorphism with translation by the skeleton
class of the added object.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

open Functor.IsCofibered

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Translate the chosen cocartesian lift associated to a right-comma
object. -/
noncomputable def secondTranslationCostructuredPushforwardMap
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredMap A B).obj X).left ⟶
      ((secondTranslationFiberFunctor A B).obj
        ((costructuredToFiber B).obj X)).1 :=
  (translateSecondFunctor A).map
    (pushforwardMap (costructuredSourceFiber X).2 X.hom)

/-- The translated chosen lift lies over the structural arrow of the
translated right-comma object. -/
theorem secondTranslationCostructuredPushforwardMap_isHomLift
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (translationProjection (C := C)).IsHomLift
      ((secondTranslationCostructuredMap A B).obj X).hom
      (secondTranslationCostructuredPushforwardMap A B X) := by
  let p := translationProjection (C := C)
  let u := pushforwardMap (costructuredSourceFiber X).2 X.hom
  have hStructural :
      ((secondTranslationCostructuredMap A B).obj X).hom = X.hom := by
    rw [secondTranslationCostructuredMap_obj_hom]
    simp
  refine IsHomLift.of_fac' p
    ((secondTranslationCostructuredMap A B).obj X).hom
    (secondTranslationCostructuredPushforwardMap A B X)
    rfl
    ((secondTranslationFiberFunctor A B).obj
      ((costructuredToFiber B).obj X)).2 ?_
  dsimp only [p, secondTranslationCostructuredPushforwardMap]
  rw [translationProjection_map_translateSecondFunctor_map]
  have hu : p.IsHomLift X.hom u := inferInstance
  simpa only [p, u, hStructural, Category.id_comp] using
    (IsHomLift.fac' p X.hom u)

/-- Objectwise comparison from translating in the right-comma category and
then retracting to the fiber, to retracting first and translating in the
fiber. -/
noncomputable def secondTranslationCostructuredToFiberApp
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (costructuredToFiber B).obj
        ((secondTranslationCostructuredMap A B).obj X) ⟶
      (secondTranslationFiberFunctor A B).obj
        ((costructuredToFiber B).obj X) :=
  fiberPushforwardFactorHom
    ((secondTranslationCostructuredMap A B).obj X).hom
    (costructuredSourceFiber
      ((secondTranslationCostructuredMap A B).obj X))
    ((secondTranslationFiberFunctor A B).obj
      ((costructuredToFiber B).obj X))
    (secondTranslationCostructuredPushforwardMap A B X)
    (secondTranslationCostructuredPushforwardMap_isHomLift A B X)

/-- Characteristic factorization of the second-translation comparison
component. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_secondTranslationCostructuredToFiberApp
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    pushforwardMap
          (costructuredSourceFiber
            ((secondTranslationCostructuredMap A B).obj X)).2
          ((secondTranslationCostructuredMap A B).obj X).hom ≫
        (secondTranslationCostructuredToFiberApp A B X).1 =
      secondTranslationCostructuredPushforwardMap A B X :=
  pushforwardMap_comp_fiberPushforwardFactor
    ((secondTranslationCostructuredMap A B).obj X).hom
    (costructuredSourceFiber
      ((secondTranslationCostructuredMap A B).obj X))
    ((secondTranslationFiberFunctor A B).obj
      ((costructuredToFiber B).obj X))
    (secondTranslationCostructuredPushforwardMap A B X)
    (secondTranslationCostructuredPushforwardMap_isHomLift A B X)

/-- Naturality of the comma-to-fiber second-translation comparison. -/
theorem secondTranslationCostructuredToFiberApp_naturality
    (A : C) (B : Translation C)
    {X Y : CostructuredArrow (translationProjection (C := C)) B}
    (f : X ⟶ Y) :
    (costructuredToFiber B).map
          ((secondTranslationCostructuredMap A B).map f) ≫
        secondTranslationCostructuredToFiberApp A B Y =
      secondTranslationCostructuredToFiberApp A B X ≫
        (secondTranslationFiberFunctor A B).map
          ((costructuredToFiber B).map f) := by
  let p := translationProjection (C := C)
  let qX := (secondTranslationCostructuredMap A B).obj X
  let qY := (secondTranslationCostructuredMap A B).obj Y
  let uX := pushforwardMap (costructuredSourceFiber X).2 X.hom
  let uY := pushforwardMap (costructuredSourceFiber Y).2 Y.hom
  let liftX := pushforwardMap (costructuredSourceFiber qX).2 qX.hom
  let liftY := pushforwardMap (costructuredSourceFiber qY).2 qY.hom
  let left :=
    (costructuredToFiber B).map
        ((secondTranslationCostructuredMap A B).map f) ≫
      secondTranslationCostructuredToFiberApp A B Y
  let right := secondTranslationCostructuredToFiberApp A B X ≫
    (secondTranslationFiberFunctor A B).map
      ((costructuredToFiber B).map f)
  apply Functor.Fiber.hom_ext
  change left.1 = right.1
  let _ : p.IsStronglyCocartesian qX.hom liftX := inferInstance
  let _ : p.IsHomLift (𝟙 B) left.1 := left.2
  let _ : p.IsHomLift (𝟙 B) right.1 := right.2
  apply Functor.IsCocartesian.ext p qX.hom liftX left.1 right.1
  change
    liftX ≫
        (((costructuredToFiber B).map
          ((secondTranslationCostructuredMap A B).map f)).1 ≫
            (secondTranslationCostructuredToFiberApp A B Y).1) =
      liftX ≫
        ((secondTranslationCostructuredToFiberApp A B X).1 ≫
          ((secondTranslationFiberFunctor A B).map
            ((costructuredToFiber B).map f)).1)
  calc
    _ = (liftX ≫
          ((costructuredToFiber B).map
            ((secondTranslationCostructuredMap A B).map f)).1) ≫
        (secondTranslationCostructuredToFiberApp A B Y).1 :=
      (Category.assoc _ _ _).symm
    _ = (((secondTranslationCostructuredMap A B).map f).left ≫
          liftY) ≫
        (secondTranslationCostructuredToFiberApp A B Y).1 := by
      dsimp only [liftX, liftY, qX, qY]
      change
        (pushforwardMap
              (costructuredSourceFiber
                ((secondTranslationCostructuredMap A B).obj X)).2
              ((secondTranslationCostructuredMap A B).obj X).hom ≫
            (costructuredToFiberMap
              ((secondTranslationCostructuredMap A B).map f)).1) ≫
            (secondTranslationCostructuredToFiberApp A B Y).1 =
          (((secondTranslationCostructuredMap A B).map f).left ≫
              pushforwardMap
                (costructuredSourceFiber
                  ((secondTranslationCostructuredMap A B).obj Y)).2
                ((secondTranslationCostructuredMap A B).obj Y).hom) ≫
            (secondTranslationCostructuredToFiberApp A B Y).1
      rw [pushforwardMap_comp_costructuredToFiberMap]
    _ = ((secondTranslationCostructuredMap A B).map f).left ≫
        (liftY ≫
          (secondTranslationCostructuredToFiberApp A B Y).1) :=
      Category.assoc _ _ _
    _ = (translateSecondFunctor A).map f.left ≫
        secondTranslationCostructuredPushforwardMap A B Y := by
      rw [pushforwardMap_comp_secondTranslationCostructuredToFiberApp,
        secondTranslationCostructuredMap_map_left]
    _ = (translateSecondFunctor A).map (f.left ≫ uY) := by
      dsimp only [secondTranslationCostructuredPushforwardMap, uY]
      exact ((translateSecondFunctor A).map_comp f.left
        (pushforwardMap (costructuredSourceFiber Y).2 Y.hom)).symm
    _ = (translateSecondFunctor A).map
        (uX ≫ ((costructuredToFiber B).map f).1) := by
      congr 1
      dsimp only [uX, uY]
      exact (pushforwardMap_comp_costructuredToFiberMap f).symm
    _ = (translateSecondFunctor A).map uX ≫
        (translateSecondFunctor A).map
          ((costructuredToFiber B).map f).1 :=
      (translateSecondFunctor A).map_comp _ _
    _ = (liftX ≫
          (secondTranslationCostructuredToFiberApp A B X).1) ≫
        (translateSecondFunctor A).map
          ((costructuredToFiber B).map f).1 := by
      rw [pushforwardMap_comp_secondTranslationCostructuredToFiberApp]
      rfl
    _ = liftX ≫
        ((secondTranslationCostructuredToFiberApp A B X).1 ≫
          (translateSecondFunctor A).map
            ((costructuredToFiber B).map f).1) :=
      Category.assoc _ _ _
    _ = _ := by
      rw [secondTranslationFiberFunctor_map_val]

/-- Second-coordinate translation commutes with the right-comma-to-fiber
comparison up to the canonical cocartesian factorization. -/
noncomputable def secondTranslationCostructuredToFiberNatTrans
    (A : C) (B : Translation C) :
    secondTranslationCostructuredMap A B ⋙ costructuredToFiber B ⟶
      costructuredToFiber B ⋙ secondTranslationFiberFunctor A B where
  app := secondTranslationCostructuredToFiberApp A B
  naturality _ _ f :=
    secondTranslationCostructuredToFiberApp_naturality A B f

section Homology

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Under the right-comma/fiber and core/fiber homology comparisons,
second-coordinate translation on a right-comma category is the core
translation action of the added object's skeleton class. -/
theorem secondTranslationCostructured_homologyMap_comp_coreComparison
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (n : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R n ≫
        ((costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom ≫
          (coreTranslationFiberHomologyIso C B R n).inv) =
      ((costructuredFiberHomologyIso
          (p := translationProjection (C := C))
          AddCommGrpCat.{u} B R n).hom ≫
        (coreTranslationFiberHomologyIso C B R n).inv) ≫
          coreTranslationHomologyMap C R n (toSkeleton A) := by
  let H : Cat.{u, u} ⥤ AddCommGrpCat.{u} :=
    categoryHomologyFunctor AddCommGrpCat.{u} R n
  have hComma :
      SSet.homologyMap
            (nerveMap (secondTranslationCostructuredMap A B)) R n ≫
          (costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom =
        (costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom ≫
          SSet.homologyMap
            (nerveMap (secondTranslationFiberFunctor A B)) R n := by
    rw [costructuredFiberHomologyIso_hom]
    change
      H.map (secondTranslationCostructuredMap A B).toCatHom ≫
          H.map (costructuredToFiber B).toCatHom =
        H.map (costructuredToFiber B).toCatHom ≫
          H.map (secondTranslationFiberFunctor A B).toCatHom
    rw [← H.map_comp, ← H.map_comp]
    exact categoryHomologyMap_eq_of_natTrans AddCommGrpCat.{u}
      (secondTranslationCostructuredToFiberNatTrans A B) R n
  have hFiber :
      (coreTranslationFiberHomologyIso C B R n).hom ≫
          SSet.homologyMap
            (nerveMap (secondTranslationFiberFunctor A B)) R n =
        SSet.homologyMap
            (nerveMap (coreLeftTranslationFunctor A)) R n ≫
          (coreTranslationFiberHomologyIso C B R n).hom := by
    change
      H.map (coreToTranslationFiber
            (⟨B.of⟩ : Core C)).toCatHom ≫
          H.map (secondTranslationFiberFunctor A B).toCatHom =
        H.map (coreLeftTranslationFunctor A).toCatHom ≫
          H.map (coreToTranslationFiber
            (⟨B.of⟩ : Core C)).toCatHom
    rw [← H.map_comp, ← H.map_comp]
    exact categoryHomologyMap_eq_of_natIso AddCommGrpCat.{u}
      (coreSecondTranslationFiberIso
        (⟨A⟩ : Core C) (⟨B.of⟩ : Core C)) R n
  have hFiberConj :
      SSet.homologyMap
            (nerveMap (secondTranslationFiberFunctor A B)) R n ≫
          (coreTranslationFiberHomologyIso C B R n).inv =
        (coreTranslationFiberHomologyIso C B R n).inv ≫
          SSet.homologyMap
            (nerveMap (coreLeftTranslationFunctor A)) R n := by
    apply (cancel_epi
      (coreTranslationFiberHomologyIso C B R n).hom).1
    calc
      (coreTranslationFiberHomologyIso C B R n).hom ≫
          (SSet.homologyMap
              (nerveMap (secondTranslationFiberFunctor A B)) R n ≫
            (coreTranslationFiberHomologyIso C B R n).inv) =
        ((coreTranslationFiberHomologyIso C B R n).hom ≫
            SSet.homologyMap
              (nerveMap (secondTranslationFiberFunctor A B)) R n) ≫
          (coreTranslationFiberHomologyIso C B R n).inv :=
        (Category.assoc _ _ _).symm
      _ = (SSet.homologyMap
              (nerveMap (coreLeftTranslationFunctor A)) R n ≫
            (coreTranslationFiberHomologyIso C B R n).hom) ≫
          (coreTranslationFiberHomologyIso C B R n).inv := by
        rw [hFiber]
      _ = SSet.homologyMap
          (nerveMap (coreLeftTranslationFunctor A)) R n := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (coreTranslationFiberHomologyIso C B R n).hom ≫
          ((coreTranslationFiberHomologyIso C B R n).inv ≫
            SSet.homologyMap
              (nerveMap (coreLeftTranslationFunctor A)) R n) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  calc
    _ = (SSet.homologyMap
            (nerveMap (secondTranslationCostructuredMap A B)) R n ≫
          (costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom) ≫
        (coreTranslationFiberHomologyIso C B R n).inv :=
      (Category.assoc _ _ _).symm
    _ = ((costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom ≫
          SSet.homologyMap
            (nerveMap (secondTranslationFiberFunctor A B)) R n) ≫
        (coreTranslationFiberHomologyIso C B R n).inv := by
      rw [hComma]
    _ = (costructuredFiberHomologyIso
          (p := translationProjection (C := C))
          AddCommGrpCat.{u} B R n).hom ≫
        (SSet.homologyMap
            (nerveMap (secondTranslationFiberFunctor A B)) R n ≫
          (coreTranslationFiberHomologyIso C B R n).inv) :=
      Category.assoc _ _ _
    _ = (costructuredFiberHomologyIso
          (p := translationProjection (C := C))
          AddCommGrpCat.{u} B R n).hom ≫
        ((coreTranslationFiberHomologyIso C B R n).inv ≫
          SSet.homologyMap
            (nerveMap (coreLeftTranslationFunctor A)) R n) := by
      rw [hFiberConj]
    _ = ((costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R n).hom ≫
          (coreTranslationFiberHomologyIso C B R n).inv) ≫
        SSet.homologyMap
          (nerveMap (coreLeftTranslationFunctor A)) R n :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [← coreTranslationHomologyMap_toSkeleton]

end Homology

end SInverseS
end CategoryTheory

end
