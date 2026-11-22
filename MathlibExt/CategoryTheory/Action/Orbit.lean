/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Action.Limits

/-!
# Coinvariants of an arbitrary monoid action

The actual single-object colimit functor, its projection, invariant descent
and equivariant naturality retain the original action and all its maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe v u wM
open CategoryTheory CategoryTheory.Limits
namespace Action
variable {C : Type u} [Category.{v} C]

section Coinvariants

variable (M : Type wM) [Monoid M] [HasColimitsOfShape (SingleObj M) C]

/-- The actual orbit functor of the original action, as its original single-object colimit. -/
def coinvariantsFunctor : Action C M ⥤ C :=
  (functorCategoryEquivalence C M).functor ⋙ colim

/-- The original action object maps to its actual orbit through the original colimit leg. -/
def coinvariantsProjection (X : Action C M) : X.V ⟶ (coinvariantsFunctor M).obj X :=
  colimit.ι ((functorCategoryEquivalence C M).functor.obj X) (SingleObj.star M)

/-- The original projection coequalizes each original action arrow. -/
@[reassoc]
theorem coinvariantsProjection_invariant (X : Action C M) (m : M) :
    (X.ρ m).asHom ≫ coinvariantsProjection M X = coinvariantsProjection M X :=
  colimit.w ((functorCategoryEquivalence C M).functor.obj X)
    (show SingleObj.star M ⟶ SingleObj.star M from m)

/-- Every original equivariant arrow has the literal orbit projection square. -/
@[reassoc]
theorem coinvariantsMap_projection {X X' : Action C M} (f : X ⟶ X') :
    coinvariantsProjection M X ≫ (coinvariantsFunctor M).map f =
      f.hom ≫ coinvariantsProjection M X' :=
  ι_colimMap ((functorCategoryEquivalence C M).functor.map f) (SingleObj.star M)

/-- The original orbit projection jointly determines arrows out of its original colimit. -/
@[ext]
theorem coinvariants_hom_ext (X : Action C M) {Z : C}
    (f g : (coinvariantsFunctor M).obj X ⟶ Z)
    (h : coinvariantsProjection M X ≫ f = coinvariantsProjection M X ≫ g) : f = g := by
  apply colimit.hom_ext
  intro j
  cases j
  exact h

/-- An invariant original coefficient arrow gives its actual action cocone. -/
def coinvariantsCocone (X : Action C M) {Z : C} (f : X.V ⟶ Z)
    (hf : ∀ m : M, (X.ρ m).asHom ≫ f = f) :
    Cocone ((functorCategoryEquivalence C M).functor.obj X) where
  pt := Z
  ι :=
    { app := fun _ => f
      naturality := fun _ _ m => by
        change (X.ρ m).asHom ≫ f = f ≫ 𝟙 Z
        rw [Category.comp_id]
        exact hf m }

/-- Invariant maps descend through the actual original orbit colimit. -/
def coinvariantsDesc (X : Action C M) {Z : C} (f : X.V ⟶ Z)
    (hf : ∀ m : M, (X.ρ m).asHom ≫ f = f) :
    (coinvariantsFunctor M).obj X ⟶ Z :=
  colimit.desc _ (coinvariantsCocone M X f hf)

/-- Orbit descent keeps the exact original projection. -/
@[reassoc]
theorem coinvariantsDesc_projection (X : Action C M) {Z : C} (f : X.V ⟶ Z)
    (hf : ∀ m : M, (X.ρ m).asHom ≫ f = f) :
    coinvariantsProjection M X ≫ coinvariantsDesc M X f hf = f :=
  colimit.ι_desc (coinvariantsCocone M X f hf) (SingleObj.star M)

end Coinvariants

end Action
