/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.LiftingTest

/-!
# Entire function owners for tagged-test preservation

The native fixed coproduct, shrinking comparison and whole Arrow
normalization retain both complete functions, their inverses, all
original maps and every original representative collection.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w s t uA vA uD vD uS vS uC vC

open CategoryTheory Limits TypeCat
open CategoryTheory.MorphismProperty.LiftingTest
open CategoryTheory.Presentable.LiftingTest

namespace CategoryTheory.Presentable.LiftingTestOwner

section FixedSums

variable {A : Type uA} [Category.{vA} A] {S : Type s} (F : S → A ⥤ Type t)

/-- Every native Discrete component has its entire original lifted map. -/
theorem fixedFamily_map_function {p q : A} (a : p ⟶ q) (k : S) :
    ((fixedFamily F).map a).app ⟨k⟩ =
      ofHom (fun z : ULift.{s} ((F k).obj p) =>
        (ULift.up ((F k).map a z.down) : ULift.{s} ((F k).obj q))) := rfl

/-- The whole coproduct forward function is the actual native coproduct comparison. -/
theorem fixedSum_hom_function (p : A) :
    (fixedSumColimitIso F).hom.app p =
      (Types.coproductIso (fun k : S => ULift.{s} ((F k).obj p))).hom ≫
        (fixedSumEquiv F p).toIso.hom := rfl

/-- The whole inverse function uses the same original value and native coproduct choice. -/
theorem fixedSum_inv_function (p : A) :
    (fixedSumColimitIso F).inv.app p =
      (fixedSumEquiv F p).toIso.inv ≫
        (Types.coproductIso (fun k : S => ULift.{s} ((F k).obj p))).inv := rfl

/-- Every original tag and whole component function survive the native coproduct injection. -/
theorem fixedSum_hom_injection (p : A) (k : S) :
    Sigma.ι (fun j : S => ULift.{s} ((F j).obj p)) k ≫
      (fixedSumColimitIso F).hom.app p =
        ofHom (fun z : ULift.{s} ((F k).obj p) => (⟨k, z.down⟩ : Σ j : S, (F j).obj p)) := by
  change (Sigma.ι (fun j : S => ULift.{s} ((F j).obj p)) k ≫
    (Types.coproductIso (fun j : S => ULift.{s} ((F j).obj p))).hom) ≫
      (fixedSumEquiv F p).toIso.hom = _
  rw [Types.coproductIso_ι_comp_hom]
  rfl

/-- Every original tag and value are restored by the entire inverse coproduct function. -/
theorem fixedSum_inv_value (p : A) (k : S) (z : (F k).obj p) :
    (fixedSumColimitIso F).inv.app p (⟨k, z⟩ : Σ j : S, (F j).obj p) =
      Sigma.ι (fun j : S => ULift.{s} ((F j).obj p)) k ⟨z⟩ := by
  change (Types.coproductIso (fun j : S => ULift.{s} ((F j).obj p))).inv
    (⟨k, ULift.up z⟩ : Σ j : S, ULift.{s} ((F j).obj p)) = _
  rfl

/-- The whole original coproduct function has its full first roundtrip. -/
theorem fixedSum_hom_inv (p : A) :
    (fixedSumColimitIso F).hom.app p ≫ (fixedSumColimitIso F).inv.app p = 𝟙 _ :=
  (fixedSumColimitIso F).app p |>.hom_inv_id

/-- The whole original coproduct function has its full inverse roundtrip. -/
theorem fixedSum_inv_hom (p : A) :
    (fixedSumColimitIso F).inv.app p ≫ (fixedSumColimitIso F).hom.app p = 𝟙 _ :=
  (fixedSumColimitIso F).app p |>.inv_hom_id

/-- Every entire original component map commutes with the forward coproduct comparison. -/
theorem fixedSum_hom_naturality {p q : A} (a : p ⟶ q) :
    colimMap ((fixedFamily F).map a) ≫ (fixedSumColimitIso F).hom.app q =
      (fixedSumColimitIso F).hom.app p ≫ (fixedSumFunctor F).map a :=
  (fixedSumColimitIso F).hom.naturality a

/-- Every entire original component map commutes with the inverse coproduct comparison. -/
theorem fixedSum_inv_naturality {p q : A} (a : p ⟶ q) :
    (fixedSumFunctor F).map a ≫ (fixedSumColimitIso F).inv.app q =
      (fixedSumColimitIso F).inv.app p ≫ colimMap ((fixedFamily F).map a) :=
  (fixedSumColimitIso F).inv.naturality a

end FixedSums

section Shrink

variable {A : Type uA} [Category.{vA} A] (F : A ⥤ Type t)
  [FunctorToTypes.Small.{w} F]

/-- The entire forward shrinking comparison decodes every original element. -/
theorem shrink_hom_function (p : A) :
    (shrinkUliftIso.{w} F).hom.app p =
      ofHom (fun z => ULift.up ((equivShrink (F.obj p)).symm z.down)) :=
  shrinkUliftIso_hom_function.{w} F p

/-- The entire inverse shrinking comparison retains every original element. -/
theorem shrink_inv_function (p : A) :
    (shrinkUliftIso.{w} F).inv.app p =
      ofHom (fun z => ULift.up (equivShrink (F.obj p) z.down)) :=
  shrinkUliftIso_inv_function.{w} F p

/-- Both full shrinking functions have their original first roundtrip. -/
theorem shrink_hom_inv (p : A) :
    (shrinkUliftIso.{w} F).hom.app p ≫ (shrinkUliftIso.{w} F).inv.app p = 𝟙 _ :=
  (shrinkUliftIso.{w} F).app p |>.hom_inv_id

/-- Both full shrinking functions have their original inverse roundtrip. -/
theorem shrink_inv_hom (p : A) :
    (shrinkUliftIso.{w} F).inv.app p ≫ (shrinkUliftIso.{w} F).hom.app p = 𝟙 _ :=
  (shrinkUliftIso.{w} F).app p |>.inv_hom_id

/-- The entire original functor map commutes with the actual forward shrinking function. -/
theorem shrink_hom_naturality {p q : A} (a : p ⟶ q) :
    (FunctorToTypes.shrink.{w} F ⋙ uliftFunctor.{t, w}).map a ≫
      (shrinkUliftIso.{w} F).hom.app q =
    (shrinkUliftIso.{w} F).hom.app p ≫ (F ⋙ uliftFunctor.{w, t}).map a :=
  (shrinkUliftIso.{w} F).hom.naturality a

/-- The entire original functor map commutes with the actual inverse shrinking function. -/
theorem shrink_inv_naturality {p q : A} (a : p ⟶ q) :
    (F ⋙ uliftFunctor.{w, t}).map a ≫ (shrinkUliftIso.{w} F).inv.app q =
      (shrinkUliftIso.{w} F).inv.app p ≫
        (FunctorToTypes.shrink.{w} F ⋙ uliftFunctor.{t, w}).map a :=
  (shrinkUliftIso.{w} F).inv.naturality a

end Shrink

section Normalized

variable {A : Type uA} [Category.{vA} A] (T : A ⥤ Arrow (Type t))
  [∀ p, Small.{w} (T.obj p).left] [∀ p, Small.{w} (T.obj p).right]

/-- The whole forward source function retains its original source value. -/
theorem normalized_hom_left_function (p : A) :
    ((normalizedUliftIso.{w} T).hom.app p).left =
      ofHom (fun z => ULift.up ((equivShrink (T.obj p).left).symm z.down)) :=
  normalizedUliftIso_hom_left_function.{w} T p

/-- The whole forward target function retains its original target value. -/
theorem normalized_hom_right_function (p : A) :
    ((normalizedUliftIso.{w} T).hom.app p).right =
      ofHom (fun z => ULift.up ((equivShrink (T.obj p).right).symm z.down)) :=
  normalizedUliftIso_hom_right_function.{w} T p

/-- The whole inverse source function restores the original source encoding. -/
theorem normalized_inv_left_function (p : A) :
    ((normalizedUliftIso.{w} T).inv.app p).left =
      ofHom (fun z => ULift.up (equivShrink (T.obj p).left z.down)) :=
  normalizedUliftIso_inv_left_function.{w} T p

/-- The whole inverse target function restores the original target encoding. -/
theorem normalized_inv_right_function (p : A) :
    ((normalizedUliftIso.{w} T).inv.app p).right =
      ofHom (fun z => ULift.up (equivShrink (T.obj p).right z.down)) :=
  normalizedUliftIso_inv_right_function.{w} T p

/-- The whole forward Arrow comparison retains the SAME original test function. -/
theorem normalized_hom_square (p : A) :
    ((normalizedUliftIso.{w} T).hom.app p).left ≫
        ((T ⋙ Functor.mapArrow uliftFunctor.{w, t}).obj p).hom =
      ((normalizedFunctor.{w} T ⋙ Functor.mapArrow uliftFunctor.{t, w}).obj p).hom ≫
        ((normalizedUliftIso.{w} T).hom.app p).right :=
  ((normalizedUliftIso.{w} T).hom.app p).w

/-- The whole inverse Arrow comparison retains the SAME original test function. -/
theorem normalized_inv_square (p : A) :
    ((normalizedUliftIso.{w} T).inv.app p).left ≫
        ((normalizedFunctor.{w} T ⋙ Functor.mapArrow uliftFunctor.{t, w}).obj p).hom =
      ((T ⋙ Functor.mapArrow uliftFunctor.{w, t}).obj p).hom ≫
        ((normalizedUliftIso.{w} T).inv.app p).right :=
  ((normalizedUliftIso.{w} T).inv.app p).w

/-- Both complete normalization functions have their whole first Arrow roundtrip. -/
theorem normalized_hom_inv (p : A) :
    (normalizedUliftIso.{w} T).hom.app p ≫ (normalizedUliftIso.{w} T).inv.app p = 𝟙 _ :=
  (normalizedUliftIso.{w} T).app p |>.hom_inv_id

/-- Both complete normalization functions have their whole inverse Arrow roundtrip. -/
theorem normalized_inv_hom (p : A) :
    (normalizedUliftIso.{w} T).inv.app p ≫ (normalizedUliftIso.{w} T).hom.app p = 𝟙 _ :=
  (normalizedUliftIso.{w} T).app p |>.inv_hom_id

/-- Both entire Arrow maps commute with the forward normalization on every original arrow. -/
theorem normalized_hom_naturality {p q : A} (a : p ⟶ q) :
    (normalizedFunctor.{w} T ⋙ Functor.mapArrow uliftFunctor.{t, w}).map a ≫
      (normalizedUliftIso.{w} T).hom.app q =
    (normalizedUliftIso.{w} T).hom.app p ≫ (T ⋙ Functor.mapArrow uliftFunctor.{w, t}).map a :=
  (normalizedUliftIso.{w} T).hom.naturality a

/-- Both entire Arrow maps commute with the inverse normalization on every original arrow. -/
theorem normalized_inv_naturality {p q : A} (a : p ⟶ q) :
    (T ⋙ Functor.mapArrow uliftFunctor.{w, t}).map a ≫ (normalizedUliftIso.{w} T).inv.app q =
      (normalizedUliftIso.{w} T).inv.app p ≫
        (normalizedFunctor.{w} T ⋙ Functor.mapArrow uliftFunctor.{t, w}).map a :=
  (normalizedUliftIso.{w} T).inv.naturality a

end Normalized

section OriginalDiagrams

variable {D : Type uD} [Category.{vD} D]
  {S : Type uS} [Category.{vS} S] [Small.{w} S]
  {C : Type uC} [Category.{vC} C] [LocallySmall.{w} C]
  {I : Type s} [Small.{w} I] (e : D ≌ S) (f : I → Arrow C)

/-- The full original representative source collection is decoded by its SAME normalization. -/
theorem diagram_hom_left_function (p : Arrow (D ⥤ C)) :
    ((normalizedUliftIso.{w} (diagramCollection.{w} e f)).hom.app p).left =
      ofHom (fun z => ULift.up
        ((equivShrink ((diagramCollection.{w} e f).obj p).left).symm z.down)) :=
  normalizedUliftIso_hom_left_function.{w} (diagramCollection.{w} e f) p

/-- The full original representative square collection is decoded by its SAME normalization. -/
theorem diagram_hom_right_function (p : Arrow (D ⥤ C)) :
    ((normalizedUliftIso.{w} (diagramCollection.{w} e f)).hom.app p).right =
      ofHom (fun z => ULift.up
        ((equivShrink ((diagramCollection.{w} e f).obj p).right).symm z.down)) :=
  normalizedUliftIso_hom_right_function.{w} (diagramCollection.{w} e f) p

/-- The full inverse source function retains every actual original representative value. -/
theorem diagram_inv_left_function (p : Arrow (D ⥤ C)) :
    ((normalizedUliftIso.{w} (diagramCollection.{w} e f)).inv.app p).left =
      ofHom (fun z => ULift.up
        (equivShrink ((diagramCollection.{w} e f).obj p).left z.down)) :=
  normalizedUliftIso_inv_left_function.{w} (diagramCollection.{w} e f) p

/-- The full inverse target function retains every actual original native square value. -/
theorem diagram_inv_right_function (p : Arrow (D ⥤ C)) :
    ((normalizedUliftIso.{w} (diagramCollection.{w} e f)).inv.app p).right =
      ofHom (fun z => ULift.up
        (equivShrink ((diagramCollection.{w} e f).obj p).right z.down)) :=
  normalizedUliftIso_inv_right_function.{w} (diagramCollection.{w} e f) p

/-- Every original diagram Arrow map acts by the SAME complete forward comparison. -/
theorem diagram_hom_naturality {p q : Arrow (D ⥤ C)} (a : p ⟶ q) :
    (diagramFunctor.{w} e f ⋙ Functor.mapArrow uliftFunctor.{max uS w, w}).map a ≫
      (normalizedUliftIso.{w} (diagramCollection.{w} e f)).hom.app q =
    (normalizedUliftIso.{w} (diagramCollection.{w} e f)).hom.app p ≫
      (diagramCollection.{w} e f ⋙ Functor.mapArrow uliftFunctor.{w, max uS w}).map a :=
  (normalizedUliftIso.{w} (diagramCollection.{w} e f)).hom.naturality a

/-- Every original diagram Arrow map acts by the SAME complete inverse comparison. -/
theorem diagram_inv_naturality {p q : Arrow (D ⥤ C)} (a : p ⟶ q) :
    (diagramCollection.{w} e f ⋙ Functor.mapArrow uliftFunctor.{w, max uS w}).map a ≫
      (normalizedUliftIso.{w} (diagramCollection.{w} e f)).inv.app q =
    (normalizedUliftIso.{w} (diagramCollection.{w} e f)).inv.app p ≫
      (diagramFunctor.{w} e f ⋙ Functor.mapArrow uliftFunctor.{max uS w, w}).map a :=
  (normalizedUliftIso.{w} (diagramCollection.{w} e f)).inv.naturality a

end OriginalDiagrams

end CategoryTheory.Presentable.LiftingTestOwner
