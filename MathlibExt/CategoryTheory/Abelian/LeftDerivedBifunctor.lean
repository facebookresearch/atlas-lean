/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Left derivation in the first variable of a bifunctor

For `F : C₁ ⥤ C₂ ⥤ D`, derive each fixed-second-variable functor and
retain the transformations induced by morphisms in `C₂`. The simultaneous
maps satisfy the interchange law. Category universes are independent and
only `C₁` needs projective resolutions.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory.Functor

open CategoryTheory Category
open scoped CategoryTheory.Prod

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  [HasProjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [∀ Y : C₂, (F.flip.obj Y).Additive]

/-- Derive a bifunctor in its first variable, with the coefficient
transformations induced by the bifunctor. -/
def leftDerivedBifunctor (n : ℕ) : C₁ ⥤ C₂ ⥤ D :=
  Functor.flip
    ((additiveFunctor C₁ D).lift F.flip (fun Y => by
        change (F.flip.obj Y).Additive
        infer_instance) ⋙
      leftDerivedDegreeFunctor C₁ D n)

/-- The derived bifunctor is additive in the resolved variable. -/
instance leftDerivedBifunctor_additive (n : ℕ) :
    (F.leftDerivedBifunctor n).Additive where
  map_add {X X'} f g := by
    ext Y
    change ((F.flip.obj Y).leftDerived n).map (f + g) =
      ((F.flip.obj Y).leftDerived n).map f + ((F.flip.obj Y).leftDerived n).map g
    apply Functor.map_add

@[simp]
theorem leftDerivedBifunctor_obj_obj (n : ℕ) (X : C₁) (Y : C₂) :
    ((F.leftDerivedBifunctor n).obj X).obj Y =
      ((F.flip.obj Y).leftDerived n).obj X :=
  rfl

@[simp]
theorem leftDerivedBifunctor_map_app (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') (Y : C₂) :
    ((F.leftDerivedBifunctor n).map f).app Y =
      ((F.flip.obj Y).leftDerived n).map f :=
  rfl

@[simp]
theorem leftDerivedBifunctor_obj_map (n : ℕ) (X : C₁)
    {Y Y' : C₂} (g : Y ⟶ Y') :
    ((F.leftDerivedBifunctor n).obj X).map g =
      (NatTrans.leftDerived (F.flip.map g) n).app X :=
  rfl

/-- The derived map in both variables, applying the first-variable map
before the coefficient transformation. -/
def leftDerivedBifunctorMap (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') {Y Y' : C₂} (g : Y ⟶ Y') :
    ((F.leftDerivedBifunctor n).obj X).obj Y ⟶
      ((F.leftDerivedBifunctor n).obj X').obj Y' :=
  ((F.flip.obj Y).leftDerived n).map f ≫
    (NatTrans.leftDerived (F.flip.map g) n).app X'

/-- Simultaneous derivation agrees with the ordinary uncurried bifunctor
map. -/
theorem leftDerivedBifunctorMap_eq_uncurry (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') {Y Y' : C₂} (g : Y ⟶ Y') :
    F.leftDerivedBifunctorMap n f g =
      ((Functor.uncurry.obj (F.leftDerivedBifunctor n)).map (f ×ₘ g)) :=
  rfl

/-- The two variable maps commute, so coefficients may be changed first. -/
@[reassoc]
theorem leftDerivedBifunctorMap_eq (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') {Y Y' : C₂} (g : Y ⟶ Y') :
    F.leftDerivedBifunctorMap n f g =
      (NatTrans.leftDerived (F.flip.map g) n).app X ≫
        ((F.flip.obj Y').leftDerived n).map f :=
  (NatTrans.leftDerived (F.flip.map g) n).naturality f

@[simp]
theorem leftDerivedBifunctorMap_id (n : ℕ) (X : C₁) (Y : C₂) :
    F.leftDerivedBifunctorMap n (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  exact (Functor.uncurry.obj (F.leftDerivedBifunctor n)).map_id (X, Y)

@[simp, reassoc]
theorem leftDerivedBifunctorMap_comp (n : ℕ)
    {X X' X'' : C₁} (f : X ⟶ X') (f' : X' ⟶ X'')
    {Y Y' Y'' : C₂} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    F.leftDerivedBifunctorMap n (f ≫ f') (g ≫ g') =
      F.leftDerivedBifunctorMap n f g ≫
        F.leftDerivedBifunctorMap n f' g' := by
  exact (Functor.uncurry.obj (F.leftDerivedBifunctor n)).map_comp (f ×ₘ g) (f' ×ₘ g')

@[simp]
theorem leftDerivedBifunctorMap_zero_left (n : ℕ)
    {X X' : C₁} {Y Y' : C₂} (g : Y ⟶ Y') :
    F.leftDerivedBifunctorMap n (0 : X ⟶ X') g = 0 := by
  unfold leftDerivedBifunctorMap
  rw [Functor.map_zero]
  apply Limits.zero_comp

@[simp]
theorem leftDerivedBifunctorMap_add_left (n : ℕ)
    {X X' : C₁} (f f' : X ⟶ X') {Y Y' : C₂} (g : Y ⟶ Y') :
    F.leftDerivedBifunctorMap n (f + f') g =
      F.leftDerivedBifunctorMap n f g + F.leftDerivedBifunctorMap n f' g := by
  unfold leftDerivedBifunctorMap
  rw [Functor.map_add]
  apply Preadditive.add_comp

section

variable [Preadditive C₂] [F.flip.Additive]

/-- A zero coefficient map induces the zero derived bifunctor map. -/
@[simp]
theorem leftDerivedBifunctorMap_zero_right (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') {Y Y' : C₂} :
    F.leftDerivedBifunctorMap n f (0 : Y ⟶ Y') = 0 := by
  unfold leftDerivedBifunctorMap
  rw [Functor.map_zero, NatTrans.leftDerived_zero, NatTrans.app_zero]
  apply Limits.comp_zero

/-- The derived bifunctor map is additive in its coefficient morphism. -/
@[simp]
theorem leftDerivedBifunctorMap_add_right (n : ℕ)
    {X X' : C₁} (f : X ⟶ X') {Y Y' : C₂} (g g' : Y ⟶ Y') :
    F.leftDerivedBifunctorMap n f (g + g') =
      F.leftDerivedBifunctorMap n f g + F.leftDerivedBifunctorMap n f g' := by
  unfold leftDerivedBifunctorMap
  rw [Functor.map_add, NatTrans.leftDerived_add, NatTrans.app_add]
  apply Preadditive.comp_add

/-- Additive coefficient maps give an additive coefficient functor after
derivation, without requiring projective resolutions in the coefficient
category. -/
instance leftDerivedBifunctor_obj_additive (n : ℕ) (X : C₁) :
    ((F.leftDerivedBifunctor n).obj X).Additive where
  map_add {Y Y'} g h := by
    change (NatTrans.leftDerived (F.flip.map (g + h)) n).app X =
      (NatTrans.leftDerived (F.flip.map g) n).app X +
        (NatTrans.leftDerived (F.flip.map h) n).app X
    rw [Functor.map_add, NatTrans.leftDerived_add, NatTrans.app_add]

end

end CategoryTheory.Functor
