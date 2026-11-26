/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Pushouts along a biproduct inclusion

Let C have zero morphisms and binary biproducts, and let b : B → B'. The square with top edge
the right injection B → X ⊞ B, left edge b, right edge id_X ⊞ b and bottom edge the right
injection B' → X ⊞ B' is a pushout.

For any pushout P of the same span, with legs inOld : X ⊞ B → P and inNew : B' → P, the
comparison e : P ≅ X ⊞ B' identifies those legs with id_X ⊞ b and the right injection. A map x
: X → X' induces a corner c_x : P → X' ⊞ B' satisfying c_x = e.hom ≫ (x ⊞ id_B'). Thus c_x is
monic when x is monic. If r : X' → X satisfies x ≫ r = id_X, then (r ⊞ id_B') ≫ e.inv is a
retraction of c_x.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsPushout

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable {X X' B B' P : C} (b : B ⟶ B')

/-- Pushout of a right biproduct injection.

In a category with zero morphisms and binary biproducts, pushing the injection B → X ⊞ B along
b : B → B' gives X ⊞ B'. The pushout legs are id_X ⊞ b : X ⊞ B → X ⊞ B' and the right
injection B' → X ⊞ B'. -/
theorem biprodInr (X : C) :
    IsPushout (biprod.inr : B ⟶ X ⊞ B) b
      (biprod.map (𝟙 X) b) (biprod.inr : B' ⟶ X ⊞ B') := by
  apply IsPushout.mk'
  · simp
  · intro T φ ψ hOld hNew
    apply biprod.hom_ext'
    · have h := congrArg (fun t => (biprod.inl : X ⟶ X ⊞ B) ≫ t) hOld
      simpa only [← Category.assoc, biprod.inl_map, Category.id_comp] using h
    · exact hNew
  · intro T aOld aNew hAgree
    refine ⟨biprod.desc ((biprod.inl : X ⟶ X ⊞ B) ≫ aOld) aNew, ?_, ?_⟩
    · apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc]
      · simpa only [biprod.inr_map_assoc, biprod.inr_desc] using hAgree.symm
    · exact biprod.inr_desc _ _

variable {b}
variable {inOld : X ⊞ B ⟶ P} {inNew : B' ⟶ P}
variable (hP : IsPushout (biprod.inr : B ⟶ X ⊞ B) b inOld inNew)

/-- Comparison of a biproduct-inclusion pushout with the replacement biproduct.

Let P be a pushout of B → X ⊞ B and b : B → B', with specified legs inOld and inNew. The
universal property gives an isomorphism e : P ≅ X ⊞ B' comparing this pushout with the
biproduct whose right factor is B'. -/
def biprodInrIso : P ≅ X ⊞ B' :=
  hP.isoIsPushout (X ⊞ B) B' (biprodInr b X)

/-- Old pushout leg under the replacement comparison.

For the comparison e : P ≅ X ⊞ B' of a pushout of B → X ⊞ B along b : B → B', the leg from X ⊞
B satisfies inOld ≫ e.hom = id_X ⊞ b. -/
theorem inOld_biprodInrIso_hom :
    inOld ≫ (biprodInrIso hP).hom = biprod.map (𝟙 X) b :=
  hP.inl_isoIsPushout_hom (X ⊞ B) B' (biprodInr b X)

/-- New pushout leg under the replacement comparison.

For the comparison e : P ≅ X ⊞ B' of a pushout of the right biproduct injection along b : B →
B', the new leg satisfies inNew ≫ e.hom = inr : B' → X ⊞ B'. -/
theorem inNew_biprodInrIso_hom :
    inNew ≫ (biprodInrIso hP).hom = (biprod.inr : B' ⟶ X ⊞ B') :=
  hP.inr_isoIsPushout_hom (X ⊞ B) B' (biprodInr b X)

/-- Corner map induced by a map on the left biproduct factor.

Let P be a pushout of the right injection B → X ⊞ B along b : B → B'. For x : X → X', define
c_x : P → X' ⊞ B' by the maps x ⊞ b on X ⊞ B and the right injection on B'. Their agreement on
B gives the required pushout descendant. -/
def biprodInrCorner (x : X ⟶ X') : P ⟶ X' ⊞ B' :=
  hP.desc (biprod.map x b) biprod.inr (by simp)

/-- Old leg of the induced biproduct corner.

For x : X → X' and the corner c_x : P → X' ⊞ B' induced from a pushout of B → X ⊞ B along b,
the composite inOld ≫ c_x is the biproduct map x ⊞ b. -/
theorem inOld_biprodInrCorner (x : X ⟶ X') :
    inOld ≫ biprodInrCorner hP x = biprod.map x b :=
  hP.inl_desc _ _ _

/-- New leg of the induced biproduct corner.

For the corner c_x : P → X' ⊞ B' induced by x : X → X', the new pushout leg satisfies inNew ≫
c_x = inr : B' → X' ⊞ B'. -/
theorem inNew_biprodInrCorner (x : X ⟶ X') :
    inNew ≫ biprodInrCorner hP x = (biprod.inr : B' ⟶ X' ⊞ B') :=
  hP.inr_desc _ _ _

/-- Formula for the corner after identifying the pushout.

If e : P ≅ X ⊞ B' is the comparison for a pushout of the right biproduct injection along b,
then the corner induced by x : X → X' satisfies c_x = e.hom ≫ (x ⊞ id_B'). Thus only the left
factor changes under this map. -/
theorem biprodInrCorner_eq (x : X ⟶ X') :
    biprodInrCorner hP x = (biprodInrIso hP).hom ≫ biprod.map x (𝟙 B') := by
  apply hP.hom_ext
  · rw [inOld_biprodInrCorner, ← Category.assoc, inOld_biprodInrIso_hom]
    apply biprod.hom_ext' <;> simp
  · rw [inNew_biprodInrCorner, ← Category.assoc, inNew_biprodInrIso_hom]
    simp only [biprod.inr_map, Category.id_comp]

/-- Monomorphism of a corner induced by a monic left-factor map.

For a pushout of B → X ⊞ B along b : B → B', a monomorphism x : X → X' induces a monomorphism
c_x : P → X' ⊞ B'. Under the comparison P ≅ X ⊞ B', this corner is x ⊞ id_B'. -/
theorem mono_biprodInrCorner (x : X ⟶ X') [Mono x] : Mono (biprodInrCorner hP x) := by
  rw [biprodInrCorner_eq]
  infer_instance

/-- Retraction map for a biproduct pushout corner.

For a pushout comparison e : P ≅ X ⊞ B' and any r : X' → X, define the map X' ⊞ B' → P as (r ⊞
id_B') ≫ e.inv. It is a retraction of the corner induced by x whenever x ≫ r = id_X. -/
def biprodInrCornerRetraction (r : X' ⟶ X) : X' ⊞ B' ⟶ P :=
  biprod.map r (𝟙 B') ≫ (biprodInrIso hP).inv

/-- Retraction equation for a split left-factor corner.

Let x : X → X' and r : X' → X satisfy x ≫ r = id_X. For the corner c_x : P → X' ⊞ B' of a
pushout of the right biproduct injection, the map (r ⊞ id_B') ≫ e.inv satisfies c_x ≫ ((r ⊞
id_B') ≫ e.inv) = id_P. -/
theorem biprodInrCorner_retraction (x : X ⟶ X') (r : X' ⟶ X) (hr : x ≫ r = 𝟙 X) :
    biprodInrCorner hP x ≫ biprodInrCornerRetraction hP r = 𝟙 P := by
  have hMap : biprod.map x (𝟙 B') ≫ biprod.map r (𝟙 B') = 𝟙 (X ⊞ B') := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_map, Category.comp_id]
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun t => t ≫ (biprod.inl : X ⟶ X ⊞ B')) hr
    · simp
  rw [biprodInrCorner_eq]
  change ((biprodInrIso hP).hom ≫ biprod.map x (𝟙 B')) ≫
    (biprod.map r (𝟙 B') ≫ (biprodInrIso hP).inv) = _
  calc
    _ = (biprodInrIso hP).hom ≫
        ((biprod.map x (𝟙 B') ≫ biprod.map r (𝟙 B')) ≫ (biprodInrIso hP).inv) := by
      simp only [Category.assoc]
    _ = (biprodInrIso hP).hom ≫ (biprodInrIso hP).inv := by
      rw [hMap, Category.id_comp]
    _ = 𝟙 P := (biprodInrIso hP).hom_inv_id

/-- Split monomorphism of a corner induced by a split left factor.

If x : X → X' is split monic, then the corner c_x : P → X' ⊞ B' induced from a pushout of B →
X ⊞ B along b : B → B' is split monic. A retraction r of x gives the corner retraction (r ⊞
id_B') ≫ e.inv. -/
theorem isSplitMono_biprodInrCorner (x : X ⟶ X') [IsSplitMono x] :
    IsSplitMono (biprodInrCorner hP x) := by
  let s := (inferInstance : IsSplitMono x).exists_splitMono.some
  exact IsSplitMono.mk' ⟨biprodInrCornerRetraction hP s.retraction,
    biprodInrCorner_retraction hP x s.retraction s.id⟩

end CategoryTheory.IsPushout

end
