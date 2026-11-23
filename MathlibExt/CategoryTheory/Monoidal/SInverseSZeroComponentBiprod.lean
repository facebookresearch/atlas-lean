/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSBiprodFunctor
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTotalTranslationAction

/-!
# Coordinatewise biproduct on the zero component of additive S⁻¹S

Coordinatewise biproduct preserves Grothendieck difference zero and hence
restricts to the identity component.  The selected pair `(0,0)` is a left
and right unit up to explicit natural isomorphisms built from the chosen
zero-biproduct unitors.

This file contains only categorical zero-component and unit data.  It makes
no realization, CGWH, H-space, homology, kernel, plus-construction, or
`Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Grothendieck difference is additive under coordinatewise biproduct. -/
@[simp]
theorem Pair.difference_pairBiprodObj (X Y : Pair C) :
    (pairBiprodObj X Y).difference = X.difference + Y.difference := by
  unfold Pair.difference pairBiprodObj
  rw [Skeleton.toSkeleton_biprod, Skeleton.toSkeleton_biprod,
    map_add, map_add]
  abel

/-- Coordinatewise biproduct restricted to the zero component. -/
noncomputable def zeroComponentBiprodFunctor :
    ZeroComponent (C := C) × ZeroComponent (C := C) ⥤
      ZeroComponent (C := C) :=
  ObjectProperty.lift (zeroComponentProperty (C := C))
    (((zeroComponentProperty (C := C)).ι.prod
      (zeroComponentProperty (C := C)).ι) ⋙
        pairBiprodFunctor) (fun X => by
          change (pairBiprodObj X.1.obj X.2.obj).difference = 0
          rw [Pair.difference_pairBiprodObj,
            X.1.property, X.2.property, add_zero])

/-- Underlying object formula for zero-component biproduct. -/
@[simp]
theorem zeroComponentBiprodFunctor_obj_obj
    (X : ZeroComponent (C := C) × ZeroComponent (C := C)) :
    (zeroComponentBiprodFunctor.obj X).obj =
      pairBiprodObj X.1.obj X.2.obj :=
  rfl

/-- Underlying morphism formula for zero-component biproduct. -/
@[simp]
theorem zeroComponentBiprodFunctor_map_hom
    {X Y : ZeroComponent (C := C) × ZeroComponent (C := C)}
    (f : X ⟶ Y) :
    (zeroComponentBiprodFunctor.map f).hom =
      Hom.biprod f.1.hom f.2.hom :=
  rfl

/-- Pair the selected zero-component base object on the left. -/
noncomputable def zeroComponentBiprodLeftPairingFunctor :
    ZeroComponent (C := C) ⥤
      ZeroComponent (C := C) × ZeroComponent (C := C) where
  obj X := (zeroComponentBaseObject (C := C), X)
  map f := (𝟙 _, f)
  map_id X := by
    apply Prod.ext <;> simp
  map_comp f g := by
    apply Prod.ext <;> simp

/-- Pair the selected zero-component base object on the right. -/
noncomputable def zeroComponentBiprodRightPairingFunctor :
    ZeroComponent (C := C) ⥤
      ZeroComponent (C := C) × ZeroComponent (C := C) where
  obj X := (X, zeroComponentBaseObject (C := C))
  map f := (f, 𝟙 _)
  map_id X := by
    apply Prod.ext <;> simp
  map_comp f g := by
    apply Prod.ext <;> simp

/-- Left multiplication by the selected base object. -/
noncomputable def zeroComponentBiprodLeftUnitFunctor :
    ZeroComponent (C := C) ⥤ ZeroComponent (C := C) :=
  zeroComponentBiprodLeftPairingFunctor ⋙ zeroComponentBiprodFunctor

/-- Right multiplication by the selected base object. -/
noncomputable def zeroComponentBiprodRightUnitFunctor :
    ZeroComponent (C := C) ⥤ ZeroComponent (C := C) :=
  zeroComponentBiprodRightPairingFunctor ⋙ zeroComponentBiprodFunctor

@[simp]
theorem zeroComponentBiprodLeftPairingFunctor_obj
    (X : ZeroComponent (C := C)) :
    zeroComponentBiprodLeftPairingFunctor.obj X =
      (zeroComponentBaseObject (C := C), X) :=
  rfl

@[simp]
theorem zeroComponentBiprodLeftPairingFunctor_map
    {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    zeroComponentBiprodLeftPairingFunctor.map f = (𝟙 _, f) :=
  rfl

@[simp]
theorem zeroComponentBiprodRightPairingFunctor_obj
    (X : ZeroComponent (C := C)) :
    zeroComponentBiprodRightPairingFunctor.obj X =
      (X, zeroComponentBaseObject (C := C)) :=
  rfl

@[simp]
theorem zeroComponentBiprodRightPairingFunctor_map
    {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    zeroComponentBiprodRightPairingFunctor.map f = (f, 𝟙 _) :=
  rfl

@[simp]
theorem zeroComponentBiprodLeftUnitFunctor_obj_obj
    (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodLeftUnitFunctor.obj X).obj =
      pairBiprodObj (zeroComponentBaseObject (C := C)).obj X.obj :=
  rfl

@[simp]
theorem zeroComponentBiprodRightUnitFunctor_obj_obj
    (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodRightUnitFunctor.obj X).obj =
      pairBiprodObj X.obj (zeroComponentBaseObject (C := C)).obj :=
  rfl

@[simp]
theorem zeroComponentBiprodLeftUnitFunctor_map_hom
    {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    (zeroComponentBiprodLeftUnitFunctor.map f).hom =
      Hom.biprod (𝟙 (zeroComponentBaseObject (C := C)).obj) f.hom :=
  rfl

@[simp]
theorem zeroComponentBiprodRightUnitFunctor_map_hom
    {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    (zeroComponentBiprodRightUnitFunctor.map f).hom =
      Hom.biprod f.hom
        (𝟙 (zeroComponentBaseObject (C := C)).obj) :=
  rfl

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
private theorem inl_inl_biprodInterchangeIso_hom
    (A B X Y : C) :
    (biprod.inl : A ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inl : A ⟶ A ⊞ X) ≫
        (biprod.inl : A ⊞ X ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  rw [biprodInterchangeIso_hom_ext]
  simp

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
private theorem inr_inl_biprodInterchangeIso_hom
    (A B X Y : C) :
    (biprod.inr : B ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inl : B ⟶ B ⊞ Y) ≫
        (biprod.inr : B ⊞ Y ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  rw [biprodInterchangeIso_hom_ext]
  simp

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
private theorem inl_inr_biprodInterchangeIso_hom
    (A B X Y : C) :
    (biprod.inl : X ⟶ X ⊞ Y) ≫
        (biprod.inr : X ⊞ Y ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inr : X ⟶ A ⊞ X) ≫
        (biprod.inl : A ⊞ X ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  rw [biprodInterchangeIso_hom_ext]
  simp

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
private theorem inr_inr_biprodInterchangeIso_hom
    (A B X Y : C) :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫
        (biprod.inr : X ⊞ Y ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inr : Y ⟶ B ⊞ Y) ≫
        (biprod.inr : B ⊞ Y ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  rw [biprodInterchangeIso_hom_ext]
  simp

namespace RawHom

/-- Raw zero-stabilized left-unitor component. -/
noncomputable abbrev biprodLeftUnitComponent (X : Pair C) :
    RawHom
      (pairBiprodObj (zeroComponentBaseObject (C := C)).obj X) X :=
  ofCoordinateIsos
    (isoZeroBiprod (isZero_zero C)).symm
    (isoZeroBiprod (isZero_zero C)).symm

/-- Raw zero-stabilized right-unitor component. -/
noncomputable abbrev biprodRightUnitComponent (X : Pair C) :
    RawHom
      (pairBiprodObj X (zeroComponentBaseObject (C := C)).obj) X :=
  ofCoordinateIsos
    (isoBiprodZero (isZero_zero C)).symm
    (isoBiprodZero (isZero_zero C)).symm

/-- Stabilizer change in left-unitor naturality:
`0 ⊞ (0 ⊞ s) ≅ s ⊞ 0`. -/
noncomputable def biprodLeftUnitStabilizerIso (s : C) :
    (0 : C) ⊞ ((0 : C) ⊞ s) ≅ s ⊞ (0 : C) :=
  ((isoZeroBiprod (isZero_zero C)).symm :
      (0 : C) ⊞ ((0 : C) ⊞ s) ≅ (0 : C) ⊞ s) ≪≫
    ((isoZeroBiprod (isZero_zero C)).symm :
      (0 : C) ⊞ s ≅ s) ≪≫
    (isoBiprodZero (isZero_zero C) : s ≅ s ⊞ (0 : C))

/-- Stabilizer change in right-unitor naturality:
`0 ⊞ (s ⊞ 0) ≅ s ⊞ 0`. -/
noncomputable def biprodRightUnitStabilizerIso (s : C) :
    (0 : C) ⊞ (s ⊞ (0 : C)) ≅ s ⊞ (0 : C) :=
  (isoZeroBiprod (isZero_zero C)).symm

private theorem biprodLeftUnit_naturality_hom
    {s X Y : C} (f : s ⊞ X ≅ Y) :
    biprod.map (biprodLeftUnitStabilizerIso s).hom
          (𝟙 ((0 : C) ⊞ X)) ≫
        (biprod.associator s (0 : C) ((0 : C) ⊞ X)).hom ≫
        biprod.map (𝟙 s)
          ((isoZeroBiprod (isZero_zero C)).symm.hom ≫
            (isoZeroBiprod (isZero_zero C)).symm.hom) ≫
        f.hom =
      (biprod.associator (0 : C) ((0 : C) ⊞ s)
          ((0 : C) ⊞ X)).hom ≫
        (biprod.mapIso (Iso.refl (0 : C))
          ((biprodInterchangeIso (0 : C) s (0 : C) X).trans
            (biprod.mapIso
              (isoZeroBiprod (isZero_zero C)).symm f))).hom ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · apply biprod.hom_ext'
      · exact (isZero_zero C).eq_of_src _ _
      · calc
          _ = (biprod.inl : s ⟶ s ⊞ X) ≫ f.hom := by
            simp only [← Category.assoc]
            apply (cancel_mono f.hom).2
            apply biprod.hom_ext <;>
              simp [biprodLeftUnitStabilizerIso, isoZeroBiprod,
                isoBiprodZero, Category.assoc]
          _ = _ := by
            simp [biprodInterchangeIso, isoZeroBiprod,
              Category.assoc]
  · apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · calc
        _ = (biprod.inr : X ⟶ s ⊞ X) ≫ f.hom := by
          simp only [← Category.assoc]
          apply (cancel_mono f.hom).2
          apply biprod.hom_ext <;>
            simp [biprodLeftUnitStabilizerIso, isoZeroBiprod,
              isoBiprodZero, Category.assoc]
        _ = _ := by
          simp [biprodInterchangeIso, isoZeroBiprod,
            Category.assoc]

/-- Representative-level naturality of the left biproduct unitor. -/
theorem biprodLeftUnit_naturality_rel {X Y : Pair C}
    (f : RawHom X Y) :
    (((RawHom.id (zeroComponentBaseObject (C := C)).obj).biprod f).comp
        (biprodLeftUnitComponent Y)).Rel
      ((biprodLeftUnitComponent X).comp f) := by
  refine ⟨biprodLeftUnitStabilizerIso f.stabilizer, ?_, ?_⟩
  · apply Iso.ext
    dsimp [biprodLeftUnitComponent, RawHom.comp, RawHom.biprod,
      RawHom.id, ofCoordinateIsos, RawHom.ofCorePair,
      stabilizerIso, biprodLeftUnitStabilizerIso,
      zeroComponentBaseObject]
    exact biprodLeftUnit_naturality_hom f.hom₁
  · apply Iso.ext
    dsimp [biprodLeftUnitComponent, RawHom.comp, RawHom.biprod,
      RawHom.id, ofCoordinateIsos, RawHom.ofCorePair,
      stabilizerIso, biprodLeftUnitStabilizerIso,
      zeroComponentBaseObject]
    exact biprodLeftUnit_naturality_hom f.hom₂

private theorem biprodRightUnit_naturality_hom
    {s X Y : C} (f : s ⊞ X ≅ Y) :
    biprod.map (biprodRightUnitStabilizerIso s).hom
          (𝟙 (X ⊞ (0 : C))) ≫
        (biprod.associator s (0 : C) (X ⊞ (0 : C))).hom ≫
        biprod.map (𝟙 s)
          ((isoZeroBiprod (isZero_zero C)).symm.hom ≫
            (isoBiprodZero (isZero_zero C)).symm.hom) ≫
        f.hom =
      (biprod.associator (0 : C) (s ⊞ (0 : C))
          (X ⊞ (0 : C))).hom ≫
        (biprod.mapIso (Iso.refl (0 : C))
          ((biprodInterchangeIso s (0 : C) X (0 : C)).trans
            (biprod.mapIso f
              (isoZeroBiprod (isZero_zero C)).symm))).hom ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom ≫
        (isoBiprodZero (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · apply biprod.hom_ext'
      · calc
          _ = (biprod.inl : s ⟶ s ⊞ X) ≫ f.hom := by
            simp only [← Category.assoc]
            apply (cancel_mono f.hom).2
            apply biprod.hom_ext <;>
              simp [biprodRightUnitStabilizerIso, isoZeroBiprod,
                isoBiprodZero, Category.assoc]
          _ = _ := by
            simp [biprodInterchangeIso, isoZeroBiprod,
              isoBiprodZero, Category.assoc]
      · exact (isZero_zero C).eq_of_src _ _
  · apply biprod.hom_ext'
    · calc
        _ = (biprod.inr : X ⟶ s ⊞ X) ≫ f.hom := by
          simp only [← Category.assoc]
          apply (cancel_mono f.hom).2
          apply biprod.hom_ext <;>
            simp [biprodRightUnitStabilizerIso, isoZeroBiprod,
              isoBiprodZero, Category.assoc]
        _ = _ := by
          simp [biprodInterchangeIso, isoZeroBiprod,
            isoBiprodZero, Category.assoc]
    · exact (isZero_zero C).eq_of_src _ _

/-- Representative-level naturality of the right biproduct unitor. -/
theorem biprodRightUnit_naturality_rel {X Y : Pair C}
    (f : RawHom X Y) :
    ((f.biprod
        (RawHom.id (zeroComponentBaseObject (C := C)).obj)).comp
        (biprodRightUnitComponent Y)).Rel
      ((biprodRightUnitComponent X).comp f) := by
  refine ⟨biprodRightUnitStabilizerIso f.stabilizer, ?_, ?_⟩
  · apply Iso.ext
    dsimp [biprodRightUnitComponent, RawHom.comp, RawHom.biprod,
      RawHom.id, ofCoordinateIsos, RawHom.ofCorePair,
      stabilizerIso, biprodRightUnitStabilizerIso,
      zeroComponentBaseObject]
    exact biprodRightUnit_naturality_hom f.hom₁
  · apply Iso.ext
    dsimp [biprodRightUnitComponent, RawHom.comp, RawHom.biprod,
      RawHom.id, ofCoordinateIsos, RawHom.ofCorePair,
      stabilizerIso, biprodRightUnitStabilizerIso,
      zeroComponentBaseObject]
    exact biprodRightUnit_naturality_hom f.hom₂

end RawHom

/-- The selected base object is a left unit for zero-component biproduct. -/
noncomputable def zeroComponentBiprodLeftUnitIso :
    zeroComponentBiprodLeftUnitFunctor ≅
      𝟭 (ZeroComponent (C := C)) :=
  NatIso.ofComponents
    (fun X => (zeroComponentProperty (C := C)).isoMk
      (pairIsoOfCoordinateIsos
        (isoZeroBiprod (isZero_zero C)).symm
        (isoZeroBiprod (isZero_zero C)).symm)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      change Hom.comp
          (Hom.biprod (𝟙 (zeroComponentBaseObject (C := C)).obj) f.hom)
          (Hom.mk (RawHom.biprodLeftUnitComponent Y.obj)) =
        Hom.comp (Hom.mk (RawHom.biprodLeftUnitComponent X.obj)) f.hom
      induction f.hom using Quotient.inductionOn with
      | _ f =>
          apply Quotient.sound
          exact RawHom.biprodLeftUnit_naturality_rel f)

/-- The selected base object is a right unit for zero-component biproduct. -/
noncomputable def zeroComponentBiprodRightUnitIso :
    zeroComponentBiprodRightUnitFunctor ≅
      𝟭 (ZeroComponent (C := C)) :=
  NatIso.ofComponents
    (fun X => (zeroComponentProperty (C := C)).isoMk
      (pairIsoOfCoordinateIsos
        (isoBiprodZero (isZero_zero C)).symm
        (isoBiprodZero (isZero_zero C)).symm)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      change Hom.comp
          (Hom.biprod f.hom
            (𝟙 (zeroComponentBaseObject (C := C)).obj))
          (Hom.mk (RawHom.biprodRightUnitComponent Y.obj)) =
        Hom.comp (Hom.mk (RawHom.biprodRightUnitComponent X.obj)) f.hom
      induction f.hom using Quotient.inductionOn with
      | _ f =>
          apply Quotient.sound
          exact RawHom.biprodRightUnit_naturality_rel f)

/-- Exact left-unitor component formula. -/
@[simp]
theorem zeroComponentBiprodLeftUnitIso_app
    (X : ZeroComponent (C := C)) :
    zeroComponentBiprodLeftUnitIso.app X =
      (zeroComponentProperty (C := C)).isoMk
        (pairIsoOfCoordinateIsos
          (isoZeroBiprod (isZero_zero C)).symm
          (isoZeroBiprod (isZero_zero C)).symm) :=
  rfl

/-- Exact right-unitor component formula. -/
@[simp]
theorem zeroComponentBiprodRightUnitIso_app
    (X : ZeroComponent (C := C)) :
    zeroComponentBiprodRightUnitIso.app X =
      (zeroComponentProperty (C := C)).isoMk
        (pairIsoOfCoordinateIsos
          (isoBiprodZero (isZero_zero C)).symm
          (isoBiprodZero (isZero_zero C)).symm) :=
  rfl

/-- Underlying quotient representative of the left-unitor hom component. -/
@[simp]
theorem zeroComponentBiprodLeftUnitIso_hom_app_hom
    (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodLeftUnitIso.hom.app X).hom =
      Hom.mk (RawHom.biprodLeftUnitComponent X.obj) :=
  rfl

/-- Underlying quotient representative of the right-unitor hom component. -/
@[simp]
theorem zeroComponentBiprodRightUnitIso_hom_app_hom
    (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodRightUnitIso.hom.app X).hom =
      Hom.mk (RawHom.biprodRightUnitComponent X.obj) :=
  rfl

/-- At the selected base object, the left and right unit arrows agree. -/
theorem zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right :
    zeroComponentBiprodLeftUnitIso.hom.app
        (zeroComponentBaseObject (C := C)) =
      zeroComponentBiprodRightUnitIso.hom.app
        (zeroComponentBaseObject (C := C)) := by
  apply ObjectProperty.hom_ext
  rw [zeroComponentBiprodLeftUnitIso_hom_app_hom,
    zeroComponentBiprodRightUnitIso_hom_app_hom]
  apply Quotient.sound
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · apply Iso.ext
    exact (isZero_zero C).eq_of_tgt _ _
  · apply Iso.ext
    exact (isZero_zero C).eq_of_tgt _ _

end SInverseS
end CategoryTheory

end
