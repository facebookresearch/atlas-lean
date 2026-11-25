/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorUnit

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace MathlibExtTest.EnrichedSphereOperatorUnit

open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (n : I)
  [HasCoproduct (weightedCoend.relations (weight d n n) S)]
  [HasCoproduct (weightedCoend.objects (weight d n n) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n n) S)
    (weightedCoend.rightMap (weight d n n) S)]

/-- The external module sees the entire chosen epsilon/unitor/coend map. -/
example : identityGenerator d S L n =
    (λ_ (𝟙_ V)).inv ≫
      (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon) ≫
      weightedCoend.ι (weight d n n) S (𝟙_ I) := rfl

/-- The unit padding cancels at the full source integrand, without a unit-law input. -/
example : (λ_ (𝟙_ V)).hom ≫ identityGenerator d S L n =
    (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon) ≫
      weightedCoend.ι (weight d n n) S (𝟙_ I) := by
  simp only [identityGenerator, Iso.hom_inv_id_assoc]

#check @CategoryTheory.Enriched.SphereOperator.identityGenerator
#print axioms CategoryTheory.Enriched.SphereOperator.identityGenerator

end MathlibExtTest.EnrichedSphereOperatorUnit

namespace MathlibExtTest.EnrichedSphereOperatorUnit

open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (n k : I)
  [HasCoproduct (weightedCoend.relations (weight d n n) S)]
  [HasCoproduct (weightedCoend.objects (weight d n n) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n n) S)
    (weightedCoend.rightMap (weight d n n) S)]
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]
  [HasCoproduct (weightedCoend.relations (weight d k k) S)]
  [HasCoproduct (weightedCoend.objects (weight d k k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k k) S)
    (weightedCoend.rightMap (weight d k k) S)]

/-- The first unit law includes every full original integrand. -/
example (b : I) :
    (identityGenerator d S L n ⊗ₘ weightedCoend.ι (weight d n k) S b) ≫
        composition d S L n n k =
      (λ_ (weightedCoend.objects (weight d n k) S b)).hom ≫
        weightedCoend.ι (weight d n k) S b :=
  identity_composition_generator d S L n k b

/-- Whole Hom extensionality gives the actual first enriched identity law. -/
example :
    (identityGenerator d S L n ⊗ₘ 𝟙 (Hom d S n k)) ≫
        composition d S L n n k = (λ_ (Hom d S n k)).hom :=
  identity_composition d S L n k

/-- The second unit law includes every full original integrand. -/
example (a : I) :
    (weightedCoend.ι (weight d n k) S a ⊗ₘ identityGenerator d S L k) ≫
        composition d S L n k k =
      (ρ_ (weightedCoend.objects (weight d n k) S a)).hom ≫
        weightedCoend.ι (weight d n k) S a :=
  composition_identity_generator d S L n k a

/-- The second enriched identity law is an equality of the entire chosen Hom maps. -/
example :
    (𝟙 (Hom d S n k) ⊗ₘ identityGenerator d S L k) ≫
        composition d S L n k k = (ρ_ (Hom d S n k)).hom :=
  composition_identity d S L n k

#check @CategoryTheory.Enriched.SphereOperator.identity_composition_generator
#check @CategoryTheory.Enriched.SphereOperator.identity_composition
#check @CategoryTheory.Enriched.SphereOperator.composition_identity_generator
#check @CategoryTheory.Enriched.SphereOperator.composition_identity
#print axioms CategoryTheory.Enriched.SphereOperator.identity_composition_generator
#print axioms CategoryTheory.Enriched.SphereOperator.identity_composition
#print axioms CategoryTheory.Enriched.SphereOperator.composition_identity_generator
#print axioms CategoryTheory.Enriched.SphereOperator.composition_identity

end MathlibExtTest.EnrichedSphereOperatorUnit
