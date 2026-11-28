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
# Comonoids from tensor-compatible maps

Let C be monoidal, X a comonoid and m : K → X a map. Suppose δ : K → K ⊗ K satisfies δ ≫ (m ⊗
m) = m ≫ Δ_X. If id_𝟙 ⊗ m, m ⊗ id_𝟙 and m ⊗ (m ⊗ m) are monic, then δ and ε_K = m ≫ ε_X give a
comonoid on K. The counit laws and coassociativity follow by canceling these specified tensor
maps against the corresponding laws on X. The map m is then a comonoid morphism.

More generally, if m : Y → Z and g ≫ m are comonoid morphisms and m ⊗ m is monic, then g : X →
Y is a comonoid morphism. The comultiplication equation follows by tensor-square cancellation
and the counit equation by compatibility with m. The object and morphism universes remain
independent.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ComonObj

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {K X : C} [ComonObj X]

/-- Comonoid structure induced by tensor compatibility and cancellation.

Let X be a comonoid in a monoidal category, m : K → X and δ : K → K ⊗ K with δ ≫ (m ⊗ m) = m ≫
Δ_X. Assuming id_𝟙 ⊗ m, m ⊗ id_𝟙 and m ⊗ (m ⊗ m) are monic, set Δ_K = δ and ε_K = m ≫ ε_X.
Cancellation of these tensor maps proves the counit and coassociativity laws. -/
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

/-- Comonoid compatibility of the inducing map.

With δ ≫ (m ⊗ m) = m ≫ Δ_X and the three specified monic tensor maps, equip K with the induced
comonoid structure Δ_K = δ and ε_K = m ≫ ε_X. Then m : K → X is a comonoid morphism,
preserving both comultiplication and counit. -/
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

/-- Comonoid compatibility detected by a tensor-square comparison.

Let X,Y,Z be comonoids in a monoidal category, g : X → Y and m : Y → Z. If m and g ≫ m are
comonoid morphisms and m ⊗ m is monic, then g is a comonoid morphism. The counit equation
follows through m, while cancellation of m ⊗ m proves the comultiplication equation. -/
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
