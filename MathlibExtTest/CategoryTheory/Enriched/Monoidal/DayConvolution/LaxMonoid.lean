/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssembly

/-!
# Public clients for the enriched lax Day monoid

Exercise independent value and index universes, the original full generator
maps, source-isomorphism transport and the stock monoid API constructed from
the original enriched coefficient.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace MathlibExtTest.EnrichedLaxDayMonoid

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

open EnrichedDayKernel

example :
    letI := ColimitMonoidal.monoidalCategory d
    MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    MonObj.one (X := (⟨S⟩ : EnrichedFunctorCat V I)) =
      GradedYoneda.extend (𝟙_ I) S L.epsilon := LaxMonoid.monObj_one d S L

example (k : I) (a : I × I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    gen d.tensorEnrichedFunctor S S k a ≫
        EnrichedFunctorCat.component (MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I))) k =
      (𝟙 ((a.1 ⊗ a.2) ⟶[V] k) ⊗ₘ L.mu a.1 a.2) ≫
        (β_ ((a.1 ⊗ a.2) ⟶[V] k) (S.obj (a.1 ⊗ a.2))).hom ≫
        MonoidalClosed.uncurry (S.map (a.1 ⊗ a.2) k) := LaxMonoid.gen_multiply d S L k a

example (k : I) (a : I × I) (f : a.1 ⊗ a.2 ⟶ k) :
    (λ_ (S.obj a.1 ⊗ S.obj a.2)).inv ≫
      (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a.1 ⊗ S.obj a.2)) ≫
      gen d.tensorEnrichedFunctor S S k a ≫
      EnrichedFunctorCat.component (LaxMonoid.multiply d S L) k =
    L.mu a.1 a.2 ≫ S.toOrdinaryFunctor.map f :=
  LaxMonoid.labelledGenerator_multiply d S L a f

example (a : I × I) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S a ≫
      EnrichedFunctorCat.component (LaxMonoid.multiply d S L) (a.1 ⊗ a.2) = L.mu a.1 a.2 :=
  LaxMonoid.unitGenerator_multiply d S L a

example (k : I) (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d S S S k X ≫
      AssociatorFlattening.flatToNested d S S S k ≫
      Input.mapAt d.tensorEnrichedFunctor (LaxMonoid.multiply d S L)
        (GradedNatTrans.unitId S) k ≫
      EnrichedFunctorCat.component (LaxMonoid.multiply d S L) k =
    (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] k) ⊗ₘ
      ((L.mu X.1.1 X.1.2 ▷ S.obj X.2) ≫ L.mu (X.1.1 ⊗ X.1.2) X.2)) ≫
      ActionFromTransformation.targetAction S ((X.1.1 ⊗ X.1.2) ⊗ X.2) k :=
  LaxMonoid.leftFlat_multiply d S L k X

example (k : I) (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d S S S k X ≫
      AssociatorRightFlattening.flatToNested d S S S k ≫
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S)
        (LaxMonoid.multiply d S L) k ≫
      EnrichedFunctorCat.component (LaxMonoid.multiply d S L) k =
    (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) ⊗ₘ
      ((S.obj X.1.1 ◁ L.mu X.1.2 X.2) ≫ L.mu X.1.1 (X.1.2 ⊗ X.2))) ≫
      ActionFromTransformation.targetAction S (X.1.1 ⊗ (X.1.2 ⊗ X.2)) k :=
  LaxMonoid.rightFlat_multiply d S L k X

example {a b : I} (e : a ≅ b) (k : I) (Q P : V)
    (c : Q ⟶ S.obj a) (h : P ⟶ (a ⟶[V] k)) :
    (h ⊗ₘ c) ≫ ActionFromTransformation.targetAction S a k =
      ((h ≫ eHomWhiskerRight V e.inv k) ⊗ₘ (c ≫ S.toOrdinaryFunctor.map e.hom)) ≫
        ActionFromTransformation.targetAction S b k := LaxMonoid.targetAction_sourceIso S e k c h

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    IsMonHom (𝟙 (⟨S⟩ : EnrichedFunctorCat V I)) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  infer_instance

example :
    letI := ColimitMonoidal.monoidalCategory d
    (LaxMonoid.unit d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ LaxMonoid.multiply d S L =
      (λ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := LaxMonoid.one_mul_law d S L

example :
    letI := ColimitMonoidal.monoidalCategory d
    ((⟨S⟩ : EnrichedFunctorCat V I) ◁ LaxMonoid.unit d S L) ≫ LaxMonoid.multiply d S L =
      (ρ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := LaxMonoid.mul_one_law d S L

example :
    letI := ColimitMonoidal.monoidalCategory d
    (LaxMonoid.multiply d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ LaxMonoid.multiply d S L =
      (α_ (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩ ⟨S⟩).hom ≫
        ((⟨S⟩ : EnrichedFunctorCat V I) ◁ LaxMonoid.multiply d S L) ≫ LaxMonoid.multiply d S L :=
  LaxMonoid.mul_assoc_law d S L

example :
    letI := ColimitMonoidal.monoidalCategory d
    (LaxMonoid.unit d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ LaxMonoid.multiply d S L =
      (λ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact MonObj.one_mul (⟨S⟩ : EnrichedFunctorCat V I)

example :
    letI := ColimitMonoidal.monoidalCategory d
    ((⟨S⟩ : EnrichedFunctorCat V I) ◁ LaxMonoid.unit d S L) ≫ LaxMonoid.multiply d S L =
      (ρ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact MonObj.mul_one (⟨S⟩ : EnrichedFunctorCat V I)

example :
    letI := ColimitMonoidal.monoidalCategory d
    (LaxMonoid.multiply d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ LaxMonoid.multiply d S L =
      (α_ (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩ ⟨S⟩).hom ≫
        ((⟨S⟩ : EnrichedFunctorCat V I) ◁ LaxMonoid.multiply d S L) ≫ LaxMonoid.multiply d S L := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact MonObj.mul_assoc (⟨S⟩ : EnrichedFunctorCat V I)

end MathlibExtTest.EnrichedLaxDayMonoid
