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

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# Term maps of biproduct cochain complexes

Let C be a preadditive category with binary biproducts, and let
f:K → K′ and g:L → L′ be maps of integer-indexed cochain complexes.
Under the evaluation isomorphisms (K ⊞ L)ʲ ≅ Kʲ ⊞ Lʲ, the
j-th component of f ⊞ g is the biproduct map fⱼ ⊞ gⱼ.

Consequently that component is monic when fⱼ and gⱼ are monic,
and split monic when both admit retractions. The splitting is the
biproduct of the two component retractions in these coordinates.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L K' L' : CochainComplex C ℤ}

/-- Let C be preadditive with binary biproducts, f:K → K′ and g:L → L′
integer-indexed cochain maps, and j an integer. For the evaluation
isomorphisms β:(K ⊞ L)ʲ ≅ Kʲ ⊞ Lʲ and
β′:(K′ ⊞ L′)ʲ ≅ K′ʲ ⊞ L′ʲ, the component formula is
β′ ∘ (f ⊞ g)ⱼ ∘ β⁻¹ = fⱼ ⊞ gⱼ. -/
theorem biprodXIso_inv_map_hom (f : K ⟶ K') (g : L ⟶ L') (j : ℤ) :
    (biprodXIso K L j).inv ≫ (biprod.map f g).f j ≫ (biprodXIso K' L' j).hom =
      biprod.map (f.f j) (g.f j) := by
  apply biprod.hom_ext'
  · have hInl : (biprod.inl : K' ⟶ K' ⊞ L').f j ≫ (biprodXIso K' L' j).hom =
        (biprod.inl : K'.X j ⟶ K'.X j ⊞ L'.X j) := by
      rw [← inl_biprodXIso_inv K' L' j, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    calc
      biprod.inl ≫ (biprodXIso K L j).inv ≫ (biprod.map f g).f j ≫
          (biprodXIso K' L' j).hom =
          ((biprod.inl : K ⟶ K ⊞ L) ≫ biprod.map f g).f j ≫
            (biprodXIso K' L' j).hom := by
        rw [inl_biprodXIso_inv_assoc, HomologicalComplex.comp_f, Category.assoc]
      _ = (f ≫ (biprod.inl : K' ⟶ K' ⊞ L')).f j ≫
          (biprodXIso K' L' j).hom := by rw [biprod.inl_map]
      _ = f.f j ≫ biprod.inl := by
        rw [HomologicalComplex.comp_f, Category.assoc, hInl]
      _ = biprod.inl ≫ biprod.map (f.f j) (g.f j) := (biprod.inl_map _ _).symm
  · have hInr : (biprod.inr : L' ⟶ K' ⊞ L').f j ≫ (biprodXIso K' L' j).hom =
        (biprod.inr : L'.X j ⟶ K'.X j ⊞ L'.X j) := by
      rw [← inr_biprodXIso_inv K' L' j, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    calc
      biprod.inr ≫ (biprodXIso K L j).inv ≫ (biprod.map f g).f j ≫
          (biprodXIso K' L' j).hom =
          ((biprod.inr : L ⟶ K ⊞ L) ≫ biprod.map f g).f j ≫
            (biprodXIso K' L' j).hom := by
        rw [inr_biprodXIso_inv_assoc, HomologicalComplex.comp_f, Category.assoc]
      _ = (g ≫ (biprod.inr : L' ⟶ K' ⊞ L')).f j ≫
          (biprodXIso K' L' j).hom := by rw [biprod.inr_map]
      _ = g.f j ≫ biprod.inr := by
        rw [HomologicalComplex.comp_f, Category.assoc, hInr]
      _ = biprod.inr ≫ biprod.map (f.f j) (g.f j) := (biprod.inr_map _ _).symm

private theorem biprodMapComponent_eq (f : K ⟶ K') (g : L ⟶ L') (j : ℤ) :
    (biprod.map f g).f j = (biprodXIso K L j).hom ≫
      biprod.map (f.f j) (g.f j) ≫ (biprodXIso K' L' j).inv := by
  rw [← cancel_epi (biprodXIso K L j).inv, ← cancel_mono (biprodXIso K' L' j).hom]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using biprodXIso_inv_map_hom f g j

/-- In a preadditive category C with binary biproducts, let f:K → K′
and g:L → L′ be integer-indexed cochain maps. If their components
fⱼ and gⱼ are monomorphisms in a fixed degree j, then the j-th
component of f ⊞ g is a monomorphism. -/
theorem mono_biprod_map_f (f : K ⟶ K') (g : L ⟶ L') (j : ℤ)
    [Mono (f.f j)] [Mono (g.f j)] : Mono ((biprod.map f g).f j) := by
  rw [biprodMapComponent_eq]
  infer_instance

/-- In a preadditive category C with binary biproducts, let f:K → K′
and g:L → L′ be integer-indexed cochain maps. If fⱼ and gⱼ are
split monomorphisms in a fixed degree j, then (f ⊞ g)ⱼ is split
monic, with retraction given by the biproduct of their retractions
under the term evaluation isomorphisms. -/
theorem isSplitMono_biprod_map_f (f : K ⟶ K') (g : L ⟶ L') (j : ℤ)
    [IsSplitMono (f.f j)] [IsSplitMono (g.f j)] : IsSplitMono ((biprod.map f g).f j) := by
  let r := (inferInstance : IsSplitMono (f.f j)).exists_splitMono.some
  let s := (inferInstance : IsSplitMono (g.f j)).exists_splitMono.some
  have hMap : biprod.map (f.f j) (g.f j) ≫ biprod.map r.retraction s.retraction =
      𝟙 (K.X j ⊞ L.X j) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_map, ← Category.assoc, r.id,
        Category.id_comp, Category.comp_id]
    · rw [biprod.inr_map_assoc, biprod.inr_map, ← Category.assoc, s.id,
        Category.id_comp, Category.comp_id]
  refine IsSplitMono.mk' ⟨(biprodXIso K' L' j).hom ≫
    biprod.map r.retraction s.retraction ≫ (biprodXIso K L j).inv, ?_⟩
  rw [biprodMapComponent_eq]
  calc
    ((biprodXIso K L j).hom ≫ biprod.map (f.f j) (g.f j) ≫
        (biprodXIso K' L' j).inv) ≫
        (biprodXIso K' L' j).hom ≫ biprod.map r.retraction s.retraction ≫
        (biprodXIso K L j).inv =
        (biprodXIso K L j).hom ≫
          (biprod.map (f.f j) (g.f j) ≫ biprod.map r.retraction s.retraction) ≫
          (biprodXIso K L j).inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (biprodXIso K L j).hom ≫ 𝟙 _ ≫ (biprodXIso K L j).inv := by rw [hMap]
    _ = 𝟙 _ := by rw [Category.id_comp, Iso.hom_inv_id]

end HomologicalComplex

end
