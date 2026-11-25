/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorUnit

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (n k : I)
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

section FirstIdentity
variable [HasCoproduct (weightedCoend.relations (weight d n n) S)]
  [HasCoproduct (weightedCoend.objects (weight d n n) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n n) S)
    (weightedCoend.rightMap (weight d n n) S)]

/-- The derived whole first unit law supplies the actual enriched category field. -/
theorem identity_comp_field :
    (λ_ (Hom d S n k)).inv ≫ identityGenerator d S L n ▷ Hom d S n k ≫
        composition d S L n n k = 𝟙 (Hom d S n k) := by
  have h := congrArg
    (fun f : (𝟙_ V) ⊗ Hom d S n k ⟶ Hom d S n k =>
      (λ_ (Hom d S n k)).inv ≫ f)
    (identity_composition d S L n k)
  simpa only [MonoidalCategory.tensorHom_id, Category.assoc,
    Iso.inv_hom_id] using h

end FirstIdentity

section SecondIdentity
variable [HasCoproduct (weightedCoend.relations (weight d k k) S)]
  [HasCoproduct (weightedCoend.objects (weight d k k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k k) S)
    (weightedCoend.rightMap (weight d k k) S)]

/-- The derived whole second unit law supplies the actual enriched category field. -/
theorem comp_identity_field :
    (ρ_ (Hom d S n k)).inv ≫ Hom d S n k ◁ identityGenerator d S L k ≫
        composition d S L n k k = 𝟙 (Hom d S n k) := by
  have h := congrArg
    (fun f : Hom d S n k ⊗ (𝟙_ V) ⟶ Hom d S n k =>
      (ρ_ (Hom d S n k)).inv ≫ f)
    (composition_identity d S L n k)
  simpa only [MonoidalCategory.id_tensorHom, Category.assoc,
    Iso.inv_hom_id] using h

end SecondIdentity
end CategoryTheory.Enriched.SphereOperator
