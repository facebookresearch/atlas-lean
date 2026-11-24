/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexUnitFunctor

/-! The whole original unit Hom map in the native tensor-padded order. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The actual full source Hom inclusion equals the original native padded unit map. -/
theorem indexHom_eq_unit_padded (n k : I) :
    indexHom d S L n k =
      (ρ_ (n ⟶[V] k)).inv ≫
        (eHomWhiskerRight V (λ_ n).hom k ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
  let H := n ⟶[V] k
  let K := ((𝟙_ I) ⊗ n) ⟶[V] k
  let p := eHomWhiskerRight V (λ_ n).hom k
  let i := weightedCoend.ι (weight d n k) S (𝟙_ I)
  have h : p ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ L.epsilon) =
      (ρ_ H).inv ≫ (p ⊗ₘ L.epsilon) := by
    rw [id_tensorHom]
    exact (rightUnitor_inv_comp_tensorHom p L.epsilon).symm
  have hIndex : indexHom d S L n k = p ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ L.epsilon) ≫ i := rfl
  calc
    _ = p ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ L.epsilon) ≫ i := hIndex
    _ = p ≫ (((ρ_ K).inv ≫ (𝟙 K ⊗ₘ L.epsilon)) ≫ i) :=
      congrArg (fun z => p ≫ z) (Category.assoc (ρ_ K).inv (𝟙 K ⊗ₘ L.epsilon) i).symm
    _ = (p ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ L.epsilon)) ≫ i := (Category.assoc _ _ _).symm
    _ = ((ρ_ H).inv ≫ (p ⊗ₘ L.epsilon)) ≫ i := congrArg (fun z => z ≫ i) h
    _ = _ := Category.assoc _ _ _

end CategoryTheory.Enriched.SphereOperator
