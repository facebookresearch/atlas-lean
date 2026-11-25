/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Comma.IsoComma
public import MathlibExt.CategoryTheory.Presentable.InverseImage

@[expose] public section

open CategoryTheory

universe vA vB vC vD uA uB uC uD

namespace IsoCommaTests

variable {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]

-- The legacy presentation keeps the independent object and morphism universes.
example (F : A ⥤ D) (G : B ⥤ D) : Type (max uA uB vD) :=
  Presentable.IsomorphismComma F G

example (F : A ⥤ D) (G : B ⥤ D) :
    Category.{max vA vB} (Presentable.IsomorphismComma F G) := inferInstance

-- Both original square fields and both comparison directions remain public.
example (F : A ⥤ D) (G : B ⥤ D) {z z' : IsoComma F G} (f : z ⟶ z') :
    (isoCommaLeft F G).map f = f.hom.left ∧
    (isoCommaRight F G).map f = f.hom.right ∧
    F.map f.hom.left ≫ (isoCommaComparison F G).hom.app z' =
      (isoCommaComparison F G).hom.app z ≫ G.map f.hom.right ∧
    G.map f.hom.right ≫ (isoCommaComparison F G).inv.app z' =
      (isoCommaComparison F G).inv.app z ≫ F.map f.hom.left :=
  ⟨isoCommaLeft_map F G f, isoCommaRight_map F G f,
    isoCommaComparison_hom_naturality F G f,
    isoCommaComparison_inv_naturality F G f⟩

variable {C : Type uC} [Category.{vC} C]

-- The legacy forward embedding remains available for an arbitrary object property,
-- and its original objects and square maps work with the lower projection API.
example (F : C ⥤ D) (P : ObjectProperty D)
    {x x' : (P.inverseImage F).FullSubcategory} (f : x ⟶ x') :
    (isoCommaLeft F P.ι).obj
        ((Presentable.inverseImageToIsomorphismComma F P).obj x) = x.obj ∧
      (isoCommaLeft F P.ι).map
        ((Presentable.inverseImageToIsomorphismComma F P).map f) = f.hom ∧
      (isoCommaComparison F P.ι).hom.app
        ((Presentable.inverseImageToIsomorphismComma F P).obj x) = 𝟙 (F.obj x.obj) :=
  ⟨rfl, rfl, rfl⟩

-- The legacy whole-component counit lemmas apply to the canonical comma objects
-- and identify the same original comparison in both directions.
example (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((Presentable.inverseImageEquivalence F P).counitIso.hom.app z).hom.right.hom =
        (isoCommaComparison F P.ι).hom.app z ∧
      ((Presentable.inverseImageEquivalence F P).counitIso.inv.app z).hom.right.hom =
        (isoCommaComparison F P.ι).inv.app z :=
  ⟨congrFun (Presentable.inverseImageEquivalence_counit_hom_right F P) z,
    congrFun (Presentable.inverseImageEquivalence_counit_inv_right F P) z⟩

-- The same original map is retained in the forward and inverse directions.
example (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    {x x' : (P.inverseImage F).FullSubcategory} (f : x ⟶ x') :
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.left = x.obj ∧
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.right.obj = F.obj x.obj ∧
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.hom = 𝟙 (F.obj x.obj) ∧
    ((inverseImageIsoCommaEquivalence F P).functor.map f).hom.left = f.hom ∧
    ((inverseImageIsoCommaEquivalence F P).functor.map f).hom.right.hom = F.map f.hom ∧
    ((inverseImageIsoCommaEquivalence F P).inverse.map
      ((inverseImageIsoCommaEquivalence F P).functor.map f)).hom = f.hom := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inverseImageIsoCommaEquivalence_functor_obj_left F P x
  · exact inverseImageIsoCommaEquivalence_functor_obj_right F P x
  · exact inverseImageIsoCommaEquivalence_functor_obj_hom F P x
  · exact inverseImageIsoCommaEquivalence_functor_map_left F P f
  · exact inverseImageIsoCommaEquivalence_functor_map_right F P f
  · simp

-- Unit and counit maps and BOTH triangles are checked on the original objects.
example (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).unitIso.hom.app x).hom = 𝟙 x.obj ∧
    ((inverseImageIsoCommaEquivalence F P).unitIso.inv.app x).hom = 𝟙 x.obj ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z).hom.left =
      𝟙 z.obj.left ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z).hom.right.hom =
      z.obj.hom ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.inv.app z).hom.left =
      𝟙 z.obj.left ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.inv.app z).hom.right.hom =
      (isoCommaComparison F P.ι).inv.app z ∧
    (inverseImageIsoCommaEquivalence F P).functor.map
        ((inverseImageIsoCommaEquivalence F P).unitIso.hom.app x) ≫
      (inverseImageIsoCommaEquivalence F P).counitIso.hom.app
        ((inverseImageIsoCommaEquivalence F P).functor.obj x) =
      𝟙 ((inverseImageIsoCommaEquivalence F P).functor.obj x) ∧
    (inverseImageIsoCommaEquivalence F P).unitIso.hom.app
        ((inverseImageIsoCommaEquivalence F P).inverse.obj z) ≫
      (inverseImageIsoCommaEquivalence F P).inverse.map
        ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z) =
      𝟙 ((inverseImageIsoCommaEquivalence F P).inverse.obj z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inverseImageIsoCommaEquivalence_unit_hom F P x
  · exact inverseImageIsoCommaEquivalence_unit_inv F P x
  · exact inverseImageIsoCommaEquivalence_counit_hom_left F P z
  · exact inverseImageIsoCommaEquivalence_counit_hom_right F P z
  · exact inverseImageIsoCommaEquivalence_counit_inv_left F P z
  · simp
  · exact inverseImageIsoCommaEquivalence_functor_triangle F P x
  · exact inverseImageIsoCommaEquivalence_inverse_triangle F P z

-- A prescribed comparison isomorphism is retained, including its actual inverse.
example (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : C) (y : D) (hy : P y) (e : F.obj x ≅ y) :
    let z : IsoComma F P.ι := ⟨⟨x, ⟨y, hy⟩, e.hom⟩, inferInstance⟩
    ((inverseImageIsoCommaEquivalence F P).inverse.obj z).obj = x ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z).hom.right.hom = e.hom ∧
    ((inverseImageIsoCommaEquivalence F P).counitIso.inv.app z).hom.right.hom = e.inv := by
  dsimp only
  refine ⟨inverseImageIsoCommaEquivalence_inverse_obj F P _,
    inverseImageIsoCommaEquivalence_counit_hom_right F P _, ?_⟩
  rw [inverseImageIsoCommaEquivalence_counit_inv_right]
  change inv e.hom = e.inv
  simp

-- The original inclusion is compared by identities in both directions.
example (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    (inverseImageIsoCommaLeftIso F P).hom.app x = 𝟙 x.obj ∧
      (inverseImageIsoCommaLeftIso F P).inv.app x = 𝟙 x.obj :=
  ⟨inverseImageIsoCommaLeftIso_hom_app F P x, inverseImageIsoCommaLeftIso_inv_app F P x⟩

end IsoCommaTests
