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
# Term coordinates of cofiber maps from commuting squares

Let C be preadditive with binary biproducts, and let c have decidable
differential relation and a predecessor in every degree. A commuting square
with source map a:F → F′ and target map b:G → G′ from φ:F → G to
ψ:F′ → G′ induces M:Cofib(φ) → Cofib(ψ).

For c.Rel(j,i), the canonical degree-j charts identify Mⱼ with
aᵢ ⊞ bⱼ:Fᵢ ⊞ Gⱼ → F′ᵢ ⊞ G′ⱼ. Thus Mⱼ is monic when aᵢ and bⱼ
are monic. Reverse component maps r and s define a reverse term map
in the same charts; if they retract aᵢ and bⱼ, this term map retracts
Mⱼ. Split monomorphisms of the two components therefore give a split
monomorphism of the cofiber component.
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

/-- Let C be preadditive with binary biproducts and let c have decidable
differential relation and a predecessor in every degree. For a
commuting square (a,b) from φ:F → G to ψ:F′ → G′ and c.Rel(j,i),
write β_φ:Cofib(φ)ⱼ ≅ Fᵢ ⊞ Gⱼ and
β_ψ:Cofib(ψ)ⱼ ≅ F′ᵢ ⊞ G′ⱼ. Its induced cofiber map M satisfies
β_ψ ∘ Mⱼ ∘ β_φ⁻¹ = aᵢ ⊞ bⱼ. -/
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

/-- Let C be preadditive with binary biproducts, c have decidable
differential relation and predecessors in every degree, and let
(a,b) be a commuting square from φ:F → G to ψ:F′ → G′.
If c.Rel(j,i) and aᵢ,bⱼ are monomorphisms, then the degree-j
component of the induced cofiber map is a monomorphism. -/
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

/-- Let C be preadditive with binary biproducts, c have decidable
differential relation, φ:F → G and ψ:F′ → G′ be complex maps,
and c.Rel(j,i). Reverse maps r:F′ᵢ → Fᵢ and s:G′ⱼ → Gⱼ define
the term map Cofib(ψ)ⱼ → Cofib(φ)ⱼ given by
β_φ⁻¹ ∘ (r ⊞ s) ∘ β_ψ, using the canonical biproduct charts. -/
def mapArrowHomTermRetraction (i j : ι) (hji : c.Rel j i)
    (r : F'.X i ⟶ F.X i) (s : G'.X j ⟶ G.X j) :
    (homotopyCofiber ψ).X j ⟶ (homotopyCofiber φ).X j :=
  (XIsoBiprod ψ j i hji).hom ≫ biprod.map r s ≫ (XIsoBiprod φ j i hji).inv

/-- Let C be preadditive with binary biproducts and c have decidable
differential relation and predecessors in every degree. For a commuting
square (a,b) from φ to ψ and c.Rel(j,i), suppose r:F′ᵢ → Fᵢ
and s:G′ⱼ → Gⱼ satisfy r∘aᵢ=1 and s∘bⱼ=1.
Then the reverse term map Rⱼ=β_φ⁻¹ ∘ (r ⊞ s) ∘ β_ψ retracts
the induced cofiber component Mⱼ: Rⱼ ∘ Mⱼ=1. -/
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

/-- Let C be preadditive with binary biproducts, c have decidable
differential relation and predecessors in every degree, and let
(a,b) be a commuting square from φ:F → G to ψ:F′ → G′.
If c.Rel(j,i) and aᵢ,bⱼ are split monomorphisms, then the degree-j
component of the induced cofiber map is split monic. -/
theorem isSplitMono_mapArrowHom_f (i j : ι) (hji : c.Rel j i)
    [IsSplitMono (a.left.f i)] [IsSplitMono (a.right.f j)] :
    IsSplitMono ((mapArrowHom φ ψ h a).f j) := by
  let r := (inferInstance : IsSplitMono (a.left.f i)).exists_splitMono.some
  let s := (inferInstance : IsSplitMono (a.right.f j)).exists_splitMono.some
  exact IsSplitMono.mk' ⟨mapArrowHomTermRetraction i j hji r.retraction s.retraction,
    mapArrowHom_f_retraction h a i j hji r.retraction s.retraction r.id s.id⟩

end HomologicalComplex.homotopyCofiber

end
