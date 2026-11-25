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
# Corners of pushouts along a biproduct inclusion

Push out the actual right biproduct inclusion along an arbitrary map.
The resulting object is canonically the original left factor plus the
new right factor. Under this comparison the actual corner induced by a
map on the left factor is that map plus an identity.

This proves monomorphism and explicit splitness of the original corner.
The original pushout and its two legs are retained throughout.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsPushout

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable {X X' B B' P : C} (b : B ⟶ B')

/-- Replace the right factor using the actual two biproduct injections. -/
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

/-- The original pushout is compared with the actual replacement biproduct. -/
def biprodInrIso : P ≅ X ⊞ B' :=
  hP.isoIsPushout (X ⊞ B) B' (biprodInr b X)

/-- The old leg becomes the original right-factor replacement map. -/
theorem inOld_biprodInrIso_hom :
    inOld ≫ (biprodInrIso hP).hom = biprod.map (𝟙 X) b :=
  hP.inl_isoIsPushout_hom (X ⊞ B) B' (biprodInr b X)

/-- The new leg becomes the actual right biproduct inclusion. -/
theorem inNew_biprodInrIso_hom :
    inNew ≫ (biprodInrIso hP).hom = (biprod.inr : B' ⟶ X ⊞ B') :=
  hP.inr_isoIsPushout_hom (X ⊞ B) B' (biprodInr b X)

/-- The original corner is the descendant of its actual two faces. -/
def biprodInrCorner (x : X ⟶ X') : P ⟶ X' ⊞ B' :=
  hP.desc (biprod.map x b) biprod.inr (by simp)

/-- The corner retains the entire old biproduct face. -/
theorem inOld_biprodInrCorner (x : X ⟶ X') :
    inOld ≫ biprodInrCorner hP x = biprod.map x b :=
  hP.inl_desc _ _ _

/-- The corner retains the actual new boundary face. -/
theorem inNew_biprodInrCorner (x : X ⟶ X') :
    inNew ≫ biprodInrCorner hP x = (biprod.inr : B' ⟶ X' ⊞ B') :=
  hP.inr_desc _ _ _

/-- The actual corner is the original left map plus the identity on the new right factor. -/
theorem biprodInrCorner_eq (x : X ⟶ X') :
    biprodInrCorner hP x = (biprodInrIso hP).hom ≫ biprod.map x (𝟙 B') := by
  apply hP.hom_ext
  · rw [inOld_biprodInrCorner, ← Category.assoc, inOld_biprodInrIso_hom]
    apply biprod.hom_ext' <;> simp
  · rw [inNew_biprodInrCorner, ← Category.assoc, inNew_biprodInrIso_hom]
    simp only [biprod.inr_map, Category.id_comp]

/-- A monomorphism on the unchanged left factor earns a monomorphic original corner. -/
theorem mono_biprodInrCorner (x : X ⟶ X') [Mono x] : Mono (biprodInrCorner hP x) := by
  rw [biprodInrCorner_eq]
  infer_instance

/-- The actual corner retraction uses the original left retraction and the same pushout chart. -/
def biprodInrCornerRetraction (r : X' ⟶ X) : X' ⊞ B' ⟶ P :=
  biprod.map r (𝟙 B') ≫ (biprodInrIso hP).inv

/-- The original corner followed by that explicit retraction is the original identity. -/
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

/-- Actual splitness of the left factor earns splitness of the original relative corner. -/
theorem isSplitMono_biprodInrCorner (x : X ⟶ X') [IsSplitMono x] :
    IsSplitMono (biprodInrCorner hP x) := by
  let s := (inferInstance : IsSplitMono x).exists_splitMono.some
  exact IsSplitMono.mk' ⟨biprodInrCornerRetraction hP s.retraction,
    biprodInrCorner_retraction hP x s.retraction s.id⟩

end CategoryTheory.IsPushout

end
