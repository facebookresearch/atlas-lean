/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Equivalence

/-!
# Isomorphism comma categories and replete inverse images

The comparison in an isomorphism comma category is an actual isomorphism.
For a replete object property, its strict inverse image is equivalent to the
isomorphism comma category of its inclusion. The unit, counit and original
component maps are explicit. This is also the canonical construction behind
the compatibility names in `CategoryTheory.Presentable`.

This is the raw construction used in Positselski, *Notes on limits of accessible
categories*, arXiv:2310.16773v3, §5 and the final remark of §8.
-/

@[expose] public section

universe vA vB vC vD uA uB uC uD

namespace CategoryTheory

open Category

variable {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]

/-- The original comma objects whose comparison morphism is invertible. -/
abbrev isoCommaProperty (F : A ⥤ D) (G : B ⥤ D) : ObjectProperty (Comma F G) :=
  fun z => IsIso z.hom

/-- The full subcategory of the original comma category whose comparison is invertible. -/
abbrev IsoComma (F : A ⥤ D) (G : B ⥤ D) :=
  (isoCommaProperty F G).FullSubcategory

instance isoCommaCategory (F : A ⥤ D) (G : B ⥤ D) : Category (IsoComma F G) :=
  inferInstanceAs (Category (isoCommaProperty F G).FullSubcategory)

instance isoCommaIsIso (F : A ⥤ D) (G : B ⥤ D) (z : IsoComma F G) : IsIso z.obj.hom :=
  z.property

instance isoCommaProperty_isClosedUnderIsomorphisms (F : A ⥤ D) (G : B ⥤ D) :
    (isoCommaProperty F G).IsClosedUnderIsomorphisms where
  of_iso {z z'} e hz := by
    have : IsIso z.hom := hz
    have : IsIso (F.map e.hom.left ≫ z'.hom) := by
      rw [e.hom.w]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map e.hom.left) z'.hom

/-- The original left projection of the isomorphism comma category. -/
def isoCommaLeft (F : A ⥤ D) (G : B ⥤ D) : IsoComma F G ⥤ A :=
  (isoCommaProperty F G).ι ⋙ Comma.fst F G

/-- The original right projection of the isomorphism comma category. -/
def isoCommaRight (F : A ⥤ D) (G : B ⥤ D) : IsoComma F G ⥤ B :=
  (isoCommaProperty F G).ι ⋙ Comma.snd F G

@[simp] theorem isoCommaLeft_obj (F : A ⥤ D) (G : B ⥤ D) (z : IsoComma F G) :
    (isoCommaLeft F G).obj z = z.obj.left := rfl

@[simp] theorem isoCommaRight_obj (F : A ⥤ D) (G : B ⥤ D) (z : IsoComma F G) :
    (isoCommaRight F G).obj z = z.obj.right := rfl

@[simp] theorem isoCommaLeft_map (F : A ⥤ D) (G : B ⥤ D)
    {z z' : IsoComma F G} (f : z ⟶ z') :
    (isoCommaLeft F G).map f = f.hom.left := rfl

@[simp] theorem isoCommaRight_map (F : A ⥤ D) (G : B ⥤ D)
    {z z' : IsoComma F G} (f : z ⟶ z') :
    (isoCommaRight F G).map f = f.hom.right := rfl

/-- The natural comparison with its original hom and inverse. -/
noncomputable def isoCommaComparison (F : A ⥤ D) (G : B ⥤ D) :
    isoCommaLeft F G ⋙ F ≅ isoCommaRight F G ⋙ G :=
  NatIso.ofComponents (fun z => @asIso D _ _ _ z.obj.hom z.property) (by
    intro z z' f
    exact f.hom.w)

@[simp] theorem isoCommaComparison_hom_app (F : A ⥤ D) (G : B ⥤ D)
    (z : IsoComma F G) :
    (isoCommaComparison F G).hom.app z = z.obj.hom := rfl

@[simp] theorem isoCommaComparison_inv_app (F : A ⥤ D) (G : B ⥤ D)
    (z : IsoComma F G) :
    (isoCommaComparison F G).inv.app z =
      (letI : IsIso z.obj.hom := z.property; inv z.obj.hom) := rfl

/-- Naturality on the original comparison arrows is the original comma square. -/
theorem isoCommaComparison_hom_naturality (F : A ⥤ D) (G : B ⥤ D)
    {z z' : IsoComma F G} (f : z ⟶ z') :
    F.map f.hom.left ≫ (isoCommaComparison F G).hom.app z' =
      (isoCommaComparison F G).hom.app z ≫ G.map f.hom.right :=
  f.hom.w

/-- Naturality on the original inverse comparisons. -/
theorem isoCommaComparison_inv_naturality (F : A ⥤ D) (G : B ⥤ D)
    {z z' : IsoComma F G} (f : z ⟶ z') :
    G.map f.hom.right ≫ (isoCommaComparison F G).inv.app z' =
      (isoCommaComparison F G).inv.app z ≫ F.map f.hom.left :=
  (isoCommaComparison F G).inv.naturality f

variable {C : Type uC} [Category.{vC} C]

section OriginalInverseImage

variable (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]

/-- Embed the original inverse image by identity comparisons, without requiring repleteness. -/
noncomputable def inverseImageToIsoComma :
    (P.inverseImage F).FullSubcategory ⥤ IsoComma F P.ι where
  obj A := by
    have hA : P (F.obj A.obj) := (P.prop_inverseImage_iff F A.obj).mp A.property
    refine ⟨{ left := A.obj, right := ⟨F.obj A.obj, hA⟩, hom := 𝟙 (F.obj A.obj) }, ?_⟩
    exact (inferInstance : IsIso (𝟙 (F.obj A.obj)))
  map f := ObjectProperty.homMk {
    left := f.hom
    right := ObjectProperty.homMk (F.map f.hom)
    w := by
      change F.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.hom
      simp }
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · apply ObjectProperty.hom_ext
      exact F.map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · apply ObjectProperty.hom_ext
      exact F.map_comp f.hom g.hom

/-- Return the original source object, transporting membership along the actual comparison. -/
noncomputable def isoCommaToInverseImage :
    IsoComma F P.ι ⥤ (P.inverseImage F).FullSubcategory where
  obj A := ⟨A.obj.left, P.prop_of_iso (asIso A.obj.hom).symm A.obj.right.property⟩
  map f := ObjectProperty.homMk f.hom.left

/-- The unit on the original inverse-image objects and their original morphisms. -/
noncomputable def inverseImageIsoCommaUnit :
    𝟭 (P.inverseImage F).FullSubcategory ≅
      inverseImageToIsoComma F P ⋙ isoCommaToInverseImage F P :=
  NatIso.ofComponents (fun A : (P.inverseImage F).FullSubcategory =>
      (P.inverseImage F).isoMk (Iso.refl A.obj))
    (by
      intro A B f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)

/-- The counit whose two maps are the original comparison and its inverse. -/
noncomputable def inverseImageIsoCommaCounit :
    isoCommaToInverseImage F P ⋙ inverseImageToIsoComma F P ≅
      𝟭 (IsoComma F P.ι) :=
  NatIso.ofComponents (fun A : IsoComma F P.ι => by
      let e : F.obj A.obj.left ≅ A.obj.right.obj :=
        @asIso D _ (F.obj A.obj.left) A.obj.right.obj A.obj.hom A.property
      exact (isoCommaProperty F P.ι).isoMk
        (Comma.isoMk (Iso.refl A.obj.left) (P.isoMk e) (by
          change F.map (𝟙 A.obj.left) ≫ A.obj.hom = 𝟙 _ ≫ A.obj.hom
          simp)))
    (by
      intro A B f
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
        simp
      · apply ObjectProperty.hom_ext
        exact f.hom.w)

/-- A replete property's strict inverse image is equivalent to its original isomorphism comma. -/
noncomputable def inverseImageIsoCommaEquivalence :
    (P.inverseImage F).FullSubcategory ≌ IsoComma F P.ι where
  functor := inverseImageToIsoComma F P
  inverse := isoCommaToInverseImage F P
  unitIso := inverseImageIsoCommaUnit F P
  counitIso := inverseImageIsoCommaCounit F P
  functor_unitIso_comp A := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change (𝟙 A.obj) ≫ 𝟙 _ = 𝟙 _
      simp
    · apply ObjectProperty.hom_ext
      change F.map (𝟙 A.obj) ≫ 𝟙 _ = 𝟙 _
      simp

end OriginalInverseImage

@[simp] theorem inverseImageIsoCommaEquivalence_functor_obj_left
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.left = x.obj := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_functor_obj_right
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.right.obj = F.obj x.obj := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_functor_obj_hom
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    ((inverseImageIsoCommaEquivalence F P).functor.obj x).obj.hom = 𝟙 (F.obj x.obj) := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_functor_map_left
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    {x x' : (P.inverseImage F).FullSubcategory} (f : x ⟶ x') :
    ((inverseImageIsoCommaEquivalence F P).functor.map f).hom.left = f.hom := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_functor_map_right
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    {x x' : (P.inverseImage F).FullSubcategory} (f : x ⟶ x') :
    ((inverseImageIsoCommaEquivalence F P).functor.map f).hom.right.hom = F.map f.hom := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_inverse_obj
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).inverse.obj z).obj = z.obj.left := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_inverse_map
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    {z z' : IsoComma F P.ι} (f : z ⟶ z') :
    ((inverseImageIsoCommaEquivalence F P).inverse.map f).hom = f.hom.left := rfl

/-- The original inverse-image inclusion is exactly the source projection of the inverse. -/
theorem inverseImageIsoCommaEquivalence_inverse_comp_inclusion
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] :
    (inverseImageIsoCommaEquivalence F P).inverse ⋙ (P.inverseImage F).ι =
      (isoCommaProperty F P.ι).ι ⋙ Comma.fst F P.ι := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_unit_hom
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    ((inverseImageIsoCommaEquivalence F P).unitIso.hom.app x).hom = 𝟙 x.obj := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_unit_inv
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    ((inverseImageIsoCommaEquivalence F P).unitIso.inv.app x).hom = 𝟙 x.obj := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_counit_hom_left
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z).hom.left =
      𝟙 z.obj.left := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_counit_hom_right
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z).hom.right.hom =
      z.obj.hom := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_counit_inv_left
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).counitIso.inv.app z).hom.left =
      𝟙 z.obj.left := rfl

@[simp] theorem inverseImageIsoCommaEquivalence_counit_inv_right
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    ((inverseImageIsoCommaEquivalence F P).counitIso.inv.app z).hom.right.hom =
      (letI : IsIso z.obj.hom := z.property; inv z.obj.hom) := rfl

/-- The triangle law at each original strict inverse-image object. -/
theorem inverseImageIsoCommaEquivalence_functor_triangle
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    (inverseImageIsoCommaEquivalence F P).functor.map
        ((inverseImageIsoCommaEquivalence F P).unitIso.hom.app x) ≫
      (inverseImageIsoCommaEquivalence F P).counitIso.hom.app
        ((inverseImageIsoCommaEquivalence F P).functor.obj x) =
      𝟙 ((inverseImageIsoCommaEquivalence F P).functor.obj x) :=
  (inverseImageIsoCommaEquivalence F P).functor_unitIso_comp x

/-- The other triangle law at each original isomorphism comma object. -/
theorem inverseImageIsoCommaEquivalence_inverse_triangle
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (z : IsoComma F P.ι) :
    (inverseImageIsoCommaEquivalence F P).unitIso.hom.app
        ((inverseImageIsoCommaEquivalence F P).inverse.obj z) ≫
      (inverseImageIsoCommaEquivalence F P).inverse.map
        ((inverseImageIsoCommaEquivalence F P).counitIso.hom.app z) =
      𝟙 ((inverseImageIsoCommaEquivalence F P).inverse.obj z) :=
  (inverseImageIsoCommaEquivalence F P).unit_inverse_comp z

/-- The forward equivalence followed by the left projection is the original inclusion. -/
noncomputable def inverseImageIsoCommaLeftIso (F : C ⥤ D) (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] :
    (inverseImageIsoCommaEquivalence F P).functor ⋙ isoCommaLeft F P.ι ≅
      (P.inverseImage F).ι :=
  NatIso.ofComponents (fun x => Iso.refl x.obj) (by
    intro x x' f
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)

@[simp] theorem inverseImageIsoCommaLeftIso_hom_app
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    (inverseImageIsoCommaLeftIso F P).hom.app x = 𝟙 x.obj := rfl

@[simp] theorem inverseImageIsoCommaLeftIso_inv_app
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (x : (P.inverseImage F).FullSubcategory) :
    (inverseImageIsoCommaLeftIso F P).inv.app x = 𝟙 x.obj := rfl

end CategoryTheory
