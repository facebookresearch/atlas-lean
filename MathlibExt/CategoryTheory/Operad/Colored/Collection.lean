/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.OneColor

/-!
# Colored symmetric collections

A colored symmetric collection is a functor from the groupoid of finite colored profiles. This file
provides the basic evaluation, relabelling, and restriction-of-colors API, together with the
equivalence with ordinary symmetric collections in the one-colored case.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

/-- Symmetric collections with a fixed type of colors. -/
abbrev ColoredSymmetricCollection (Color : Type u) (V : Type w) [Category.{v} V] :=
  ColoredProfile Color ⥤ V

namespace ColoredSymmetricCollection

variable {Color : Type u} {Color' : Type*}
variable {V : Type w} [Category.{v} V]

/-- Evaluation of a colored symmetric collection at a profile. -/
abbrev eval (X : ColoredSymmetricCollection Color V) (P : ColoredProfile Color) : V :=
  X.obj P

/-- Relabelling along a color-preserving profile equivalence. -/
def relabel (X : ColoredSymmetricCollection Color V) {P Q : ColoredProfile Color}
    (e : P ⟶ Q) : X.eval P ⟶ X.eval Q :=
  X.map e

/-- The relabelling isomorphism induced by a color-preserving profile equivalence. -/
noncomputable def relabelIso (X : ColoredSymmetricCollection Color V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) : X.eval P ≅ X.eval Q :=
  X.mapIso (asIso e)

@[simp]
theorem relabelIso_hom (X : ColoredSymmetricCollection Color V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (X.relabelIso e).hom = X.relabel e :=
  rfl

@[simp]
theorem relabelIso_inv (X : ColoredSymmetricCollection Color V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (X.relabelIso e).inv = X.relabel (Groupoid.inv e) := by
  simp [relabelIso, relabel, Groupoid.inv_eq_inv]

@[simp]
theorem relabel_id (X : ColoredSymmetricCollection Color V) (P : ColoredProfile Color) :
    X.relabel (𝟙 P) = 𝟙 (X.eval P) := by
  exact X.map_id P

theorem relabel_comp (X : ColoredSymmetricCollection Color V)
    {P Q R : ColoredProfile Color} (e : P ⟶ Q) (f : Q ⟶ R) :
    X.relabel (e ≫ f) = X.relabel e ≫ X.relabel f := by
  exact X.map_comp e f

/-- Collection evaluation of the identity profile equivalence. -/
theorem relabel_refl (X : ColoredSymmetricCollection Color V)
    (P : ColoredProfile Color) :
    X.map (ColoredProfile.Hom.refl P) = 𝟙 (X.obj P) := by
  rw [ColoredProfile.Hom.refl_eq_id]
  exact X.map_id P

/-- Restrict a collection along a function of color types. -/
def restrictColors (f : Color → Color') (X : ColoredSymmetricCollection Color' V) :
    ColoredSymmetricCollection Color V :=
  ColoredProfile.mapColorsFunctor f ⋙ X

/-- Restriction along a function of colors, functorially in the collection. -/
def restrictColorsFunctor (f : Color → Color') :
    ColoredSymmetricCollection Color' V ⥤ ColoredSymmetricCollection Color V :=
  (Functor.whiskeringLeft _ _ _).obj (ColoredProfile.mapColorsFunctor f)

@[simp]
theorem restrictColors_obj (f : Color → Color') (X : ColoredSymmetricCollection Color' V)
    (P : ColoredProfile Color) :
    (restrictColors f X).obj P = X.obj (P.mapColors f) :=
  rfl

@[simp]
theorem restrictColors_map (f : Color → Color') (X : ColoredSymmetricCollection Color' V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (restrictColors f X).map e = X.map (e.mapColors f) :=
  rfl

@[simp]
theorem restrictColorsFunctor_obj (f : Color → Color')
    (X : ColoredSymmetricCollection Color' V) :
    (restrictColorsFunctor f).obj X = restrictColors f X :=
  rfl

@[simp]
theorem restrictColors_id (X : ColoredSymmetricCollection Color V) :
    restrictColors id X = X :=
  rfl

@[simp]
theorem restrictColors_comp {Color'' : Type*} (f : Color → Color')
    (g : Color' → Color'') (X : ColoredSymmetricCollection Color'' V) :
    restrictColors f (restrictColors g X) = restrictColors (g ∘ f) X :=
  rfl

/-- Restriction along the identity function is the identity functor. -/
theorem restrictColorsFunctor_id :
    restrictColorsFunctor (V := V) (id : Color → Color) = 𝟭 _ :=
  rfl

/-- Restriction along a composite is the composite of the restriction functors. -/
theorem restrictColorsFunctor_comp {Color'' : Type*} (f : Color → Color')
    (g : Color' → Color'') :
    restrictColorsFunctor (V := V) (g ∘ f) =
      restrictColorsFunctor g ⋙ restrictColorsFunctor f :=
  rfl

/-- Ordinary symmetric collections are equivalent to one-colored symmetric collections. -/
noncomputable def oneColorEquivalence :
    SymmetricCollection V ≌ ColoredSymmetricCollection PUnit V :=
  ColoredProfile.oneColorEquivalence.congrLeft

@[simp]
theorem oneColorEquivalence_functor_obj (X : SymmetricCollection V) :
    oneColorEquivalence.functor.obj X =
      ColoredProfile.forgetOneColorFunctor ⋙ X :=
  rfl

@[simp]
theorem oneColorEquivalence_inverse_obj (X : ColoredSymmetricCollection PUnit V) :
    oneColorEquivalence.inverse.obj X =
      ColoredProfile.oneColorFunctor ⋙ X :=
  rfl

@[simp]
theorem oneColorEquivalence_functor_obj_obj (X : SymmetricCollection V)
    (P : ColoredProfile PUnit) :
    (oneColorEquivalence.functor.obj X).obj P =
      X.obj (ColoredProfile.forgetOneColorFunctor.obj P) :=
  rfl

@[simp]
theorem oneColorEquivalence_inverse_obj_obj (X : ColoredSymmetricCollection PUnit V)
    (A : FinBijGroupoid) :
    (oneColorEquivalence.inverse.obj X).obj A =
      X.obj (ColoredProfile.oneColorFunctor.obj A) :=
  rfl

@[simp]
theorem oneColorEquivalence_functor_map_app {X Y : SymmetricCollection V} (α : X ⟶ Y)
    (P : ColoredProfile PUnit) :
    (oneColorEquivalence.functor.map α).app P =
      α.app (ColoredProfile.forgetOneColorFunctor.obj P) :=
  rfl

@[simp]
theorem oneColorEquivalence_inverse_map_app
    {X Y : ColoredSymmetricCollection PUnit V} (α : X ⟶ Y) (A : FinBijGroupoid) :
    (oneColorEquivalence.inverse.map α).app A =
      α.app (ColoredProfile.oneColorFunctor.obj A) :=
  rfl

end ColoredSymmetricCollection

end CategoryTheory.Operad
