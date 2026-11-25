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

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid structure on a tensor-stable subobject

An original comultiplication that factors through the tensor square of a
monomorphism induces actual comonoid laws by tensor monomorphism cancellation.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ComonObj

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {K X : C} [ComonObj X]

/-- Restrict an actual comonoid to a subobject stable under its original comultiplication. -/
@[instance_reducible]
def ofTensorStableMono (m : K ⟶ X) (δ : K ⟶ K ⊗ K)
    (hδ : δ ≫ (m ⊗ₘ m) = m ≫ ComonObj.comul)
    [Mono (𝟙 (𝟙_ C) ⊗ₘ m)] [Mono (m ⊗ₘ 𝟙 (𝟙_ C))]
    [Mono (m ⊗ₘ (m ⊗ₘ m))] : ComonObj K := by
  refine {
    counit := m ≫ ComonObj.counit
    comul := δ
    counit_comul := ?_
    comul_counit := ?_
    comul_assoc := ?_ }
  · have h : ((m ≫ ComonObj.counit) ⊗ₘ 𝟙 K) ≫ (𝟙 (𝟙_ C) ⊗ₘ m) =
        (m ⊗ₘ m) ≫ (ComonObj.counit ⊗ₘ 𝟙 X) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    apply (cancel_mono (𝟙 (𝟙_ C) ⊗ₘ m)).mp
    simpa only [tensorHom_id, id_tensorHom] using
      (show (δ ≫ ((m ≫ ComonObj.counit) ⊗ₘ 𝟙 K)) ≫ (𝟙 (𝟙_ C) ⊗ₘ m) =
          (λ_ K).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ m) from by
        rw [Category.assoc, h, ← Category.assoc, hδ, Category.assoc]
        simpa only [tensorHom_id, id_tensorHom, ComonObj.counit_comul] using
          leftUnitor_inv_naturality m)
  · have h : (𝟙 K ⊗ₘ (m ≫ ComonObj.counit)) ≫ (m ⊗ₘ 𝟙 (𝟙_ C)) =
        (m ⊗ₘ m) ≫ (𝟙 X ⊗ₘ ComonObj.counit) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    apply (cancel_mono (m ⊗ₘ 𝟙 (𝟙_ C))).mp
    simpa only [tensorHom_id, id_tensorHom] using
      (show (δ ≫ (𝟙 K ⊗ₘ (m ≫ ComonObj.counit))) ≫ (m ⊗ₘ 𝟙 (𝟙_ C)) =
          (ρ_ K).inv ≫ (m ⊗ₘ 𝟙 (𝟙_ C)) from by
        rw [Category.assoc, h, ← Category.assoc, hδ, Category.assoc]
        simpa only [tensorHom_id, id_tensorHom, ComonObj.comul_counit] using
          rightUnitor_inv_naturality m)
  · have hL : (𝟙 K ⊗ₘ δ) ≫ (m ⊗ₘ (m ⊗ₘ m)) =
        (m ⊗ₘ m) ≫ (𝟙 X ⊗ₘ ComonObj.comul) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hδ]
    have hR : (δ ⊗ₘ 𝟙 K) ≫ ((m ⊗ₘ m) ⊗ₘ m) =
        (m ⊗ₘ m) ≫ (ComonObj.comul ⊗ₘ 𝟙 X) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hδ]
    have hA : (α_ K K K).hom ≫ (m ⊗ₘ (m ⊗ₘ m)) =
        ((m ⊗ₘ m) ⊗ₘ m) ≫ (α_ X X X).hom := (associator_naturality m m m).symm
    apply (cancel_mono (m ⊗ₘ (m ⊗ₘ m))).mp
    simpa only [tensorHom_id, id_tensorHom, Category.assoc] using
      (show (δ ≫ (𝟙 K ⊗ₘ δ)) ≫ (m ⊗ₘ (m ⊗ₘ m)) =
          (δ ≫ (δ ⊗ₘ 𝟙 K) ≫ (α_ K K K).hom) ≫ (m ⊗ₘ (m ⊗ₘ m)) from by
        calc
          _ = m ≫ ComonObj.comul ≫ (𝟙 X ⊗ₘ ComonObj.comul) := by
            rw [Category.assoc, hL, ← Category.assoc, hδ, Category.assoc]
          _ = m ≫ ComonObj.comul ≫ (ComonObj.comul ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom := by
            simpa only [tensorHom_id, id_tensorHom, Category.assoc] using
              congrArg (fun f => m ≫ f) (ComonObj.comul_assoc X)
          _ = _ := by
            rw [Category.assoc, Category.assoc, hA]
            rw [← Category.assoc (δ ⊗ₘ 𝟙 K), hR]
            simp only [← Category.assoc, hδ])

lemma ofTensorStableMono_isComonHom (m : K ⟶ X) (δ : K ⟶ K ⊗ K)
    (hδ : δ ≫ (m ⊗ₘ m) = m ≫ ComonObj.comul)
    [Mono (𝟙 (𝟙_ C) ⊗ₘ m)] [Mono (m ⊗ₘ 𝟙 (𝟙_ C))]
    [Mono (m ⊗ₘ (m ⊗ₘ m))] :
    letI := ofTensorStableMono m δ hδ
    IsComonHom m := by
  let := ofTensorStableMono m δ hδ
  exact ⟨rfl, hδ.symm⟩

end CategoryTheory.ComonObj

namespace CategoryTheory

open MonoidalCategory
variable {C : Type*} [Category* C] [MonoidalCategory C]
variable {X Y Z : C} [ComonObj X] [ComonObj Y] [ComonObj Z]

/-- An original factor is a comonoid map when its tensor-square comparison is monic. -/
lemma isComonHom_of_postcomp_tensorMono (g : X ⟶ Y) (m : Y ⟶ Z)
    [IsComonHom m] [IsComonHom (g ≫ m)] [Mono (m ⊗ₘ m)] : IsComonHom g := by
  constructor
  · calc
      g ≫ ComonObj.counit = g ≫ m ≫ ComonObj.counit := by rw [IsComonHom.hom_counit m]
      _ = ComonObj.counit := by rw [← Category.assoc, IsComonHom.hom_counit]
  · apply (cancel_mono (m ⊗ₘ m)).mp
    calc
      (g ≫ ComonObj.comul) ≫ (m ⊗ₘ m) = (g ≫ m) ≫ ComonObj.comul := by
        rw [Category.assoc, ← IsComonHom.hom_comul m, Category.assoc]
      _ = ComonObj.comul ≫ ((g ≫ m) ⊗ₘ (g ≫ m)) := IsComonHom.hom_comul _
      _ = (ComonObj.comul ≫ (g ⊗ₘ g)) ≫ (m ⊗ₘ m) := by
        rw [Category.assoc, tensorHom_comp_tensorHom]

end CategoryTheory
