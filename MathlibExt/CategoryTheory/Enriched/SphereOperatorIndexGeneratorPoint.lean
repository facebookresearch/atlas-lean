/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition

/-!
# Actual ordinary points of the original operator index generator

The full index generator retains the original associator, identity-fixed
left tensor arrow and ordinary composition. Its unit-graded point is the
actual ordinary composite of those maps, derived from the enriched ordinary
and tensor compatibility equations. No target generator law is a premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]

/-- The original full index generator carries the actual ordinary source arrows. -/
theorem indexGenerator_point (d : EnrichedMonoidalCategoryData V I)
    (n k l a b : I) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫
      indexGenerator d n k l a b =
        eHomEquiv V ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  let L : ((a ⊗ n) ⟶[V] k) ⟶ ((b ⊗ (a ⊗ n)) ⟶[V] (b ⊗ k)) :=
    (λ_ ((a ⊗ n) ⟶[V] k)).inv ≫
      (eId V b ⊗ₘ 𝟙 ((a ⊗ n) ⟶[V] k)) ≫ d.tensorMap b b (a ⊗ n) k
  have hL : eHomEquiv V f ≫ L = eHomEquiv V (b ◁ f) := by
    dsimp only [L]
    rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
      ← eHomEquiv_id V b, d.tensorMap_eHomEquiv, id_tensorHom]
  have hDefinition : indexGenerator d n k l a b =
      (L ⊗ₘ 𝟙 ((b ⊗ k) ⟶[V] l)) ≫ eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l ≫
        eHomWhiskerRight V (α_ b a n).hom l := by
    simp only [indexGenerator, L, eHomWhiskerRight, tensorHom_id, Category.assoc]
  rw [hDefinition]
  rw [tensorHom_comp_tensorHom_assoc, hL, Category.comp_id]
  rw [← Category.assoc _ (eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l)
    (eHomWhiskerRight V (α_ b a n).hom l)]
  rw [← Category.assoc, ← eHomEquiv_comp]
  exact eHomEquiv_comp_eHomWhiskerRight (V := V) (C := I)
    (α_ b a n).hom ((b ◁ f) ≫ g)

end CategoryTheory.Enriched.SphereOperator
