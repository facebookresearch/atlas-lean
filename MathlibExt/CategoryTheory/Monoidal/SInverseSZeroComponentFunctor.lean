/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentModelTransport

/-!
# Actual additive functors on the original zero component

The existing Pair functor's Grothendieck difference equation earns the zero
property. Restriction therefore uses the same Pair objects and arrows. Its
inclusion Iso is the stock full-subcategory lift comparison. The final helper
lifts an already constructed Pair-level Iso through the full inclusion; it
does not assume or assert the remaining telescope scalar naturality.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Algebra

universe uC vC uD vD uJ vJ

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

/-- The existing difference map sends each actual zero-component object to zero. -/
theorem pairFunctor_zeroProperty (F : C ⥤ D) [F.Additive]
    (X : ZeroComponent (C := C)) :
    zeroComponentProperty (C := D) ((pairFunctor F).obj X.obj) := by
  let k := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))
  have h : ((pairFunctor F).obj X.obj).difference = k X.obj.difference :=
    ((components_characteristic F).1 X.obj).symm
  change ((pairFunctor F).obj X.obj).difference = 0
  exact h.trans ((congrArg k X.property).trans k.map_zero)

/-- Restrict the same additive Pair functor, using its earned actual zero property. -/
@[expose] def zeroComponentFunctor (F : C ⥤ D) [F.Additive] :
    ZeroComponent (C := C) ⥤ ZeroComponent (C := D) :=
  (zeroComponentProperty (C := D)).lift
    ((zeroComponentProperty (C := C)).ι ⋙ pairFunctor F)
    (pairFunctor_zeroProperty F)

/-- The restricted object's Pair view is the original Pair-functor object. -/
theorem zeroComponentFunctor_obj_obj (F : C ⥤ D) [F.Additive]
    (X : ZeroComponent (C := C)) :
    ((zeroComponentFunctor F).obj X).obj = (pairFunctor F).obj X.obj :=
  ObjectProperty.ι_obj_lift_obj
    (zeroComponentProperty (C := D))
    ((zeroComponentProperty (C := C)).ι ⋙ pairFunctor F)
    (pairFunctor_zeroProperty F) X

/-- The whole inclusion comparison keeps all the original Pair-functor arrows. -/
def zeroComponentFunctorInclusionIso (F : C ⥤ D) [F.Additive] :
    zeroComponentFunctor F ⋙ (zeroComponentProperty (C := D)).ι ≅
      (zeroComponentProperty (C := C)).ι ⋙ pairFunctor F :=
  (zeroComponentProperty (C := D)).liftCompιIso
    ((zeroComponentProperty (C := C)).ι ⋙ pairFunctor F)
    (pairFunctor_zeroProperty F)

/-- A constructed whole Pair-level Iso lifts through the same full zero inclusion. -/
def liftZeroComponentNatIso {J : Type uJ} [Category.{vJ} J]
    (A B : J ⥤ ZeroComponent (C := D))
    (e : A ⋙ (zeroComponentProperty (C := D)).ι ≅
      B ⋙ (zeroComponentProperty (C := D)).ι) : A ≅ B :=
  NatIso.ofComponents
    (fun X => (zeroComponentProperty (C := D)).isoMk (e.app X))
    (by
      intro X Y a
      apply ObjectProperty.hom_ext
      exact e.hom.naturality a)

/-- The full zero inclusion sends each lifted component to its actual Pair component. -/
theorem liftZeroComponentNatIso_inclusion_app {J : Type uJ} [Category.{vJ} J]
    (A B : J ⥤ ZeroComponent (C := D))
    (e : A ⋙ (zeroComponentProperty (C := D)).ι ≅
      B ⋙ (zeroComponentProperty (C := D)).ι) (X : J) :
    (zeroComponentProperty (C := D)).ι.mapIso ((liftZeroComponentNatIso A B e).app X) =
      e.app X := by
  let p := zeroComponentProperty (C := D)
  let app : ∀ X : J, A.obj X ≅ B.obj X := fun X => p.isoMk (e.app X)
  have hNat : ∀ {X Y : J} (a : X ⟶ Y), A.map a ≫ (app Y).hom = (app X).hom ≫ B.map a := by
    intro X Y a
    apply ObjectProperty.hom_ext
    exact e.hom.naturality a
  have hCtor : liftZeroComponentNatIso A B e = NatIso.ofComponents app hNat := rfl
  have hApp : (liftZeroComponentNatIso A B e).app X = app X :=
    (congrArg (fun q : A ≅ B => q.app X) hCtor).trans (NatIso.ofComponents.app app hNat X)
  apply Iso.ext
  exact congrArg (fun q : A.obj X ≅ B.obj X => (p.ι.mapIso q).hom) hApp

end CategoryTheory.SInverseS

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uZeroIncludeSourceObj uZeroIncludeSourceHom uZeroIncludeTargetObj uZeroIncludeTargetHom

namespace CategoryTheory.SInverseS

variable {C : Type uZeroIncludeSourceObj} [Category.{uZeroIncludeSourceHom} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uZeroIncludeTargetObj} [Category.{uZeroIncludeTargetHom} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private theorem zeroComponentFunctorInclusionIsoAppValueComputed
    (F : C ⥤ D) [F.Additive] (X : ZeroComponent (C := C)) :
    (zeroComponentFunctorInclusionIso F).app X =
      eqToIso (zeroComponentFunctor_obj_obj F X) := by
  apply Iso.ext
  rfl

/-- EVERY original proper zero-functor inclusion component has its SAME
actual full-subcategory object transport in the original four category worlds. -/
public theorem zeroComponentFunctorInclusionIso_app_value
    (F : C ⥤ D) [F.Additive] (X : ZeroComponent (C := C)) :
    (zeroComponentFunctorInclusionIso F).app X =
      eqToIso (zeroComponentFunctor_obj_obj F X) :=
  zeroComponentFunctorInclusionIsoAppValueComputed F X

end CategoryTheory.SInverseS

end
