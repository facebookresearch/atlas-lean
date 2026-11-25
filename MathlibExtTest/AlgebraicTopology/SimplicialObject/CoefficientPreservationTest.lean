/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientPreservation

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

namespace MathlibExtTest.CoefficientPreservation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) (k : ℕ)

section Latching

variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D]
  [PreservesColimitsOfShape (latchingIndex k) F]

example : latchingObjectFunctor (C := C) k ⋙ F ≅
    (whiskeringRight SimplexCategoryᵒᵖ C D).obj F ⋙ latchingObjectFunctor k :=
  coefficientLatchingObjectIso F k

example (X : SimplicialObject C) (a : latchingIndex k) :
    latchingι (X ⋙ F) k a ≫ (coefficientLatchingObjectIso F k).inv.app X =
      F.map (latchingι X k a) :=
  (coefficientLatchingObject_legs F k X a).2

example (X : SimplicialObject C) :
    (coefficientLatchingObjectIso F k).hom.app X ≫ latchingMap (X ⋙ F) k =
      F.map (latchingMap X k) :=
  (coefficientLatchingMap_equations F k X).1

variable [HasPushouts C] [HasPushouts D] [PreservesColimitsOfShape WalkingSpan F]

example : relativeLatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow ≅
    ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
      relativeLatchingMapArrowFunctor (C := D) k :=
  coefficientRelativeLatchingArrowIso F k

example {f g : Arrow (SimplicialObject C)} (τ : f ⟶ g) :
    (relativeLatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow).map τ ≫
        (coefficientRelativeLatchingArrowIso F k).hom.app g =
      (coefficientRelativeLatchingArrowIso F k).hom.app f ≫
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
          relativeLatchingMapArrowFunctor k).map τ :=
  (coefficientRelativeLatchingArrowIso F k).hom.naturality τ

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    let a := (coefficientRelativeLatchingArrowIso F k).app (Arrow.mk f)
    pushout.inr (latchingMap (X ⋙ F) k) ((latchingObjectFunctor k).map (whiskerRight f F)) ≫
        a.inv.left = (coefficientLatchingObjectIso F k).inv.app Y ≫
          F.map (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)) :=
  (coefficientRelativeLatching_equations F k f).2.2.2.1

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    let a := (coefficientRelativeLatchingArrowIso F k).app (Arrow.mk f)
    a.hom.left ≫ relativeLatchingMap (whiskerRight f F) k =
      F.map (relativeLatchingMap f k) := by
  let a := (coefficientRelativeLatchingArrowIso F k).app (Arrow.mk f)
  have h : a.hom.left ≫ relativeLatchingMap (whiskerRight f F) k =
      F.map (relativeLatchingMap f k) ≫ a.hom.right := a.hom.w
  have hi : a.hom.right = 𝟙 (F.obj (Y.obj (op ⦋k⦌))) :=
    (coefficientRelativeLatching_equations F k f).2.2.2.2.1
  exact h.trans ((congrArg (fun j => F.map (relativeLatchingMap f k) ≫ j) hi).trans
    (Category.comp_id _))

end Latching

section Matching

variable [HasLimitsOfShape (matchingIndex k) C]
  [HasLimitsOfShape (matchingIndex k) D]
  [PreservesLimitsOfShape (matchingIndex k) F]

example : matchingObjectFunctor (C := C) k ⋙ F ≅
    (whiskeringRight SimplexCategoryᵒᵖ C D).obj F ⋙ matchingObjectFunctor k :=
  coefficientMatchingObjectIso F k

example (X : SimplicialObject C) (a : matchingIndex k) :
    (coefficientMatchingObjectIso F k).inv.app X ≫ F.map (matchingπ X k a) =
      matchingπ (X ⋙ F) k a :=
  (coefficientMatchingObject_legs F k X a).2

example (X : SimplicialObject C) :
    matchingMap (X ⋙ F) k ≫ (coefficientMatchingObjectIso F k).inv.app X =
      F.map (matchingMap X k) :=
  (coefficientMatchingMap_equations F k X).2

variable [HasPullbacks C] [HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

example : relativeMatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow ≅
    ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
      relativeMatchingMapArrowFunctor (C := D) k :=
  coefficientRelativeMatchingArrowIso F k

example {f g : Arrow (SimplicialObject C)} (τ : f ⟶ g) :
    (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
          relativeMatchingMapArrowFunctor k).map τ ≫
        (coefficientRelativeMatchingArrowIso F k).inv.app g =
      (coefficientRelativeMatchingArrowIso F k).inv.app f ≫
        (relativeMatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow).map τ :=
  (coefficientRelativeMatchingArrowIso F k).inv.naturality τ

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    let a := (coefficientRelativeMatchingArrowIso F k).app (Arrow.mk f)
    a.inv.right ≫ F.map (pullback.snd (matchingMap Y k) ((matchingObjectFunctor k).map f)) =
      pullback.snd (matchingMap (Y ⋙ F) k) ((matchingObjectFunctor k).map (whiskerRight f F)) ≫
        (coefficientMatchingObjectIso F k).inv.app X :=
  (coefficientRelativeMatching_equations F k f).2.2.2.1

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    let a := (coefficientRelativeMatchingArrowIso F k).app (Arrow.mk f)
    F.map (relativeMatchingMap f k) ≫ a.hom.right =
      relativeMatchingMap (whiskerRight f F) k := by
  let a := (coefficientRelativeMatchingArrowIso F k).app (Arrow.mk f)
  have h : a.hom.left ≫ relativeMatchingMap (whiskerRight f F) k =
      F.map (relativeMatchingMap f k) ≫ a.hom.right := a.hom.w
  have hi : a.hom.left = 𝟙 (F.obj (X.obj (op ⦋k⦌))) :=
    (coefficientRelativeMatching_equations F k f).2.2.2.2.1
  exact h.symm.trans ((congrArg (fun j => j ≫ relativeMatchingMap (whiskerRight f F) k) hi).trans
    (Category.id_comp _))

end Matching

section EquivalenceLatching

variable (e : C ≌ D) (k : ℕ)
variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D] [HasPushouts C] [HasPushouts D]

example (f : Arrow (SimplicialObject C)) :
    let A := mapArrowEquivalence e
    let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let α := coefficientRelativeLatchingArrowIso e.functor k
    let β := coefficientRelativeLatchingArrowIso e.inverse k
    A.unitIso.app ((relativeLatchingMapArrowFunctor k).obj f) ≪≫
        A.inverse.mapIso (α.app f) ≪≫ β.app (B.functor.obj f) =
      (relativeLatchingMapArrowFunctor k).mapIso (B.unitIso.app f) := by
  let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  exact (coefficientRelativeLatching_unit_counit e k f (B.functor.obj f)).1

example (g : Arrow (SimplicialObject D)) :
    let A := mapArrowEquivalence e
    let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let α := coefficientRelativeLatchingArrowIso e.functor k
    let β := coefficientRelativeLatchingArrowIso e.inverse k
    A.functor.mapIso (β.app g) ≪≫ α.app (B.inverse.obj g) ≪≫
        (relativeLatchingMapArrowFunctor k).mapIso (B.counitIso.app g) =
      A.counitIso.app ((relativeLatchingMapArrowFunctor k).obj g) := by
  let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  exact (coefficientRelativeLatching_unit_counit e k (B.inverse.obj g) g).2

end EquivalenceLatching

section EquivalenceMatching

variable (e : C ≌ D) (k : ℕ)
variable [HasLimitsOfShape (matchingIndex k) C]
  [HasLimitsOfShape (matchingIndex k) D] [HasPullbacks C] [HasPullbacks D]

example (f : Arrow (SimplicialObject C)) :
    let A := mapArrowEquivalence e
    let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let α := coefficientRelativeMatchingArrowIso e.functor k
    let β := coefficientRelativeMatchingArrowIso e.inverse k
    A.unitIso.app ((relativeMatchingMapArrowFunctor k).obj f) ≪≫
        A.inverse.mapIso (α.app f) ≪≫ β.app (B.functor.obj f) =
      (relativeMatchingMapArrowFunctor k).mapIso (B.unitIso.app f) := by
  let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  exact (coefficientRelativeMatching_unit_counit e k f (B.functor.obj f)).1

example (g : Arrow (SimplicialObject D)) :
    let A := mapArrowEquivalence e
    let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let α := coefficientRelativeMatchingArrowIso e.functor k
    let β := coefficientRelativeMatchingArrowIso e.inverse k
    A.functor.mapIso (β.app g) ≪≫ α.app (B.inverse.obj g) ≪≫
        (relativeMatchingMapArrowFunctor k).mapIso (B.counitIso.app g) =
      A.counitIso.app ((relativeMatchingMapArrowFunctor k).obj g) := by
  let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  exact (coefficientRelativeMatching_unit_counit e k (B.inverse.obj g) g).2

end EquivalenceMatching

end MathlibExtTest.CoefficientPreservation
