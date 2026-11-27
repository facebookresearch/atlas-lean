/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The canonical additive-functor biproduct square

The original mapBiprod Isos and the original biprod.map give the square.
Their public lift/projection formulas prove it in both coordinates. No
biproduct compatibility or square equation is supplied as a premise.
Source and target object/Hom worlds remain independent.
-/

noncomputable section

open CategoryTheory.Limits

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]

omit [HasBinaryBiproducts D] in
/-- The canonical mapBiprod comparison is natural for every pair of original morphisms. -/
public theorem mapBiprod_additive_naturality (F : C ⥤ D) [F.Additive]
    {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (F.mapBiprod X Y).hom ≫ biprod.map (F.map f) (F.map g) =
      F.map (biprod.map f g) ≫ (F.mapBiprod X' Y').hom := by
  apply biprod.hom_ext
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.map_fst,
      biprod.lift_fst, biprod.lift_fst_assoc, ← F.map_comp]
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.map_snd,
      biprod.lift_snd, biprod.lift_snd_assoc, ← F.map_comp]


omit [HasBinaryBiproducts D] in
/-- The inverse comparison square retains the original mapped pair of arrows. -/
public theorem mapBiprod_additive_inv_naturality (F : C ⥤ D) [F.Additive]
    {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod X' Y').inv =
      (F.mapBiprod X Y).inv ≫ F.map (biprod.map f g) := by
  let e : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y := F.mapBiprod X Y
  let e' : F.obj (X' ⊞ Y') ≅ F.obj X' ⊞ F.obj Y' := F.mapBiprod X' Y'
  let M : F.obj X ⊞ F.obj Y ⟶ F.obj X' ⊞ F.obj Y' := biprod.map (F.map f) (F.map g)
  let P : F.obj (X ⊞ Y) ⟶ F.obj (X' ⊞ Y') := F.map (biprod.map f g)
  have h : e.hom ≫ M = P ≫ e'.hom := mapBiprod_additive_naturality F f g
  change M ≫ e'.inv = e.inv ≫ P
  apply (cancel_epi e.hom).1
  have hLeft : e.hom ≫ (M ≫ e'.inv) = P := by
    calc
      _ = (e.hom ≫ M) ≫ e'.inv := (Category.assoc e.hom M e'.inv).symm
      _ = (P ≫ e'.hom) ≫ e'.inv :=
        congrArg (fun k : F.obj (X ⊞ Y) ⟶ F.obj X' ⊞ F.obj Y' => k ≫ e'.inv) h
      _ = P ≫ (e'.hom ≫ e'.inv) := Category.assoc P e'.hom e'.inv
      _ = P ≫ 𝟙 (F.obj (X' ⊞ Y')) :=
        congrArg (fun k : F.obj (X' ⊞ Y') ⟶ F.obj (X' ⊞ Y') => P ≫ k) e'.hom_inv_id
      _ = P := Category.comp_id P
  have hRight : e.hom ≫ (e.inv ≫ P) = P := by
    calc
      _ = (e.hom ≫ e.inv) ≫ P := (Category.assoc e.hom e.inv P).symm
      _ = 𝟙 (F.obj (X ⊞ Y)) ≫ P :=
        congrArg (fun k : F.obj (X ⊞ Y) ⟶ F.obj (X ⊞ Y) => k ≫ P) e.hom_inv_id
      _ = P := Category.id_comp P
  exact hLeft.trans hRight.symm

end CategoryTheory.Functor

end
