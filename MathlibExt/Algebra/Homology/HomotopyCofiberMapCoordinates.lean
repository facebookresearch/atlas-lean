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

public import MathlibExt.Algebra.Homology.HomotopyCofiber
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Original homotopy-cofiber maps in their actual term coordinates

The strict-square map is the biproduct of the original shifted source
component and the original target component under the native term
isomorphisms. These readouts give monomorphisms and split monomorphisms
of the original map, without replacing its complex or its term objects.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G F' G' : HomologicalComplex C c} {φ : F ⟶ G} {ψ : F' ⟶ G'}
variable (h : ∀ j, ∃ i, c.Rel i j) (a : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- The native term charts retain both entire components of the original strict-square map. -/
theorem XIsoBiprod_inv_mapArrowHom_hom (i j : ι) (hji : c.Rel j i)
 :
    (XIsoBiprod φ j i hji).inv ≫ (mapArrowHom φ ψ h a).f j ≫
        (XIsoBiprod ψ j i hji).hom = biprod.map (a.left.f i) (a.right.f j) := by
  apply biprod.hom_ext'
  · simp only [inl_XIsoBiprod_inv_assoc, inlX_mapArrowHom_assoc,
      inlX_XIsoBiprod_hom, biprod.inl_map]
    rfl
  · simp only [inr_XIsoBiprod_inv_assoc, inrX_mapArrowHom_assoc,
      inrX_XIsoBiprod_hom, biprod.inr_map]
    rfl

/-- The original strict-square map is monomorphic at this term when its two components are. -/
theorem mono_mapArrowHom_f (i j : ι) (hji : c.Rel j i)
    [Mono (a.left.f i)] [Mono (a.right.f j)] : Mono ((mapArrowHom φ ψ h a).f j) := by
  have hf : (mapArrowHom φ ψ h a).f j =
      (XIsoBiprod φ j i hji).hom ≫ biprod.map (a.left.f i) (a.right.f j) ≫
        (XIsoBiprod ψ j i hji).inv := by
    calc
      _ = (XIsoBiprod φ j i hji).hom ≫
          ((XIsoBiprod φ j i hji).inv ≫ (mapArrowHom φ ψ h a).f j ≫
            (XIsoBiprod ψ j i hji).hom) ≫ (XIsoBiprod ψ j i hji).inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc,
          Iso.hom_inv_id, Category.comp_id]
      _ = _ := by
        rw [XIsoBiprod_inv_mapArrowHom_hom]
        rfl
  rw [hf]
  infer_instance

/-- The original component retraction uses the actual two term charts
and supplied component retractions. -/
def mapArrowHomTermRetraction (i j : ι) (hji : c.Rel j i)
    (r : F'.X i ⟶ F.X i) (s : G'.X j ⟶ G.X j) :
    (homotopyCofiber ψ).X j ⟶ (homotopyCofiber φ).X j :=
  (XIsoBiprod ψ j i hji).hom ≫ biprod.map r s ≫ (XIsoBiprod φ j i hji).inv

/-- The original strict-square component followed by that retraction is the original identity. -/
theorem mapArrowHom_f_retraction (i j : ι) (hji : c.Rel j i)
    (r : F'.X i ⟶ F.X i) (s : G'.X j ⟶ G.X j)
    (hr : a.left.f i ≫ r = 𝟙 (F.X i)) (hs : a.right.f j ≫ s = 𝟙 (G.X j)) :
    (mapArrowHom φ ψ h a).f j ≫ mapArrowHomTermRetraction i j hji r s =
      𝟙 ((homotopyCofiber φ).X j) := by
  have hMap : biprod.map (a.left.f i) (a.right.f j) ≫ biprod.map r s =
      𝟙 (F.X i ⊞ G.X j) := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_map]
      calc
        _ = (a.left.f i ≫ r) ≫ (biprod.inl : F.X i ⟶ F.X i ⊞ G.X j) :=
          (Category.assoc _ _ _).symm
        _ = 𝟙 (F.X i) ≫ biprod.inl := congrArg (fun t => t ≫ biprod.inl) hr
        _ = biprod.inl := Category.id_comp _
        _ = biprod.inl ≫ 𝟙 _ := (Category.comp_id _).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_map]
      calc
        _ = (a.right.f j ≫ s) ≫ (biprod.inr : G.X j ⟶ F.X i ⊞ G.X j) :=
          (Category.assoc _ _ _).symm
        _ = 𝟙 (G.X j) ≫ biprod.inr := congrArg (fun t => t ≫ biprod.inr) hs
        _ = biprod.inr := Category.id_comp _
        _ = biprod.inr ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [← cancel_epi (XIsoBiprod φ j i hji).inv]
  calc
    _ = ((XIsoBiprod φ j i hji).inv ≫ (mapArrowHom φ ψ h a).f j ≫
        (XIsoBiprod ψ j i hji).hom) ≫ biprod.map r s ≫ (XIsoBiprod φ j i hji).inv := by
      simp only [mapArrowHomTermRetraction, Category.assoc]
    _ = biprod.map (a.left.f i) (a.right.f j) ≫ biprod.map r s ≫
        (XIsoBiprod φ j i hji).inv := by
      rw [XIsoBiprod_inv_mapArrowHom_hom]
      rfl
    _ = (XIsoBiprod φ j i hji).inv := by
      rw [← Category.assoc, hMap]
      exact Category.id_comp _
    _ = _ := (Category.comp_id _).symm

/-- The original strict-square term map is split mono when its two original components are. -/
theorem isSplitMono_mapArrowHom_f (i j : ι) (hji : c.Rel j i)
    [IsSplitMono (a.left.f i)] [IsSplitMono (a.right.f j)] :
    IsSplitMono ((mapArrowHom φ ψ h a).f j) := by
  let r := (inferInstance : IsSplitMono (a.left.f i)).exists_splitMono.some
  let s := (inferInstance : IsSplitMono (a.right.f j)).exists_splitMono.some
  exact IsSplitMono.mk' ⟨mapArrowHomTermRetraction i j hji r.retraction s.retraction,
    mapArrowHom_f_retraction h a i j hji r.retraction s.retraction r.id s.id⟩

end HomologicalComplex.homotopyCofiber

end
