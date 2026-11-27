/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidCommutativity

/-!
# Public clients of the genuine enriched Day braiding and commutative monoid

The source and value universes are independent. Every target structure is
constructed from the source enriched data and colimits. Full Hom generators,
both original coend faces and whole hexagons remain visible to clients.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedDayKernel
open scoped MonoidalClosed

namespace MathlibExtTest.EnrichedDayBraiding

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (b : EnrichedBraidedMonoidalCategoryData V I d)
  (F G H : EnrichedFunctorCat V I)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

example :
    letI := ColimitMonoidal.monoidalCategory d
    BraidedCategory (EnrichedFunctorCat V I) := BraidingMonoidal.braidedCategory d b

example :
    letI := ColimitMonoidal.monoidalCategory d
    SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b

example :
    letI := ColimitMonoidal.monoidalCategory d
    F ⊗ G = (Input.bifunctor d.tensorEnrichedFunctor).obj (F, G) :=
  ColimitMonoidal.tensorObj_eq d F G

example :
    letI := ColimitMonoidal.monoidalCategory d
    (α_ F G H) = AssociatorConstruction.functorIso d
      F.toEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor :=
  ColimitMonoidal.associator_eq d F G H

example :
    letI := ColimitMonoidal.monoidalCategory d
    𝟙_ (EnrichedFunctorCat V I) = ⟨GradedYoneda.representable (V := V) (𝟙_ I)⟩ :=
  ColimitMonoidal.tensorUnit_eq d

example (k : I) (a : I × I) :
    gen d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k a ≫
        BraidingComponents.component d b F.toEnrichedFunctor G.toEnrichedFunctor k =
      (eHomWhiskerRight V (β_ a.1 a.2).inv k ⊗ₘ
        (β_ (F.toEnrichedFunctor.obj a.1) (G.toEnrichedFunctor.obj a.2)).hom) ≫
        gen d.tensorEnrichedFunctor G.toEnrichedFunctor F.toEnrichedFunctor k (a.2, a.1) :=
  BraidingComponents.gen_component d b F.toEnrichedFunctor G.toEnrichedFunctor k a

example (k : I) :
    Balanced d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k (fun a =>
      gen d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k a ≫
        BraidingComponents.component d b F.toEnrichedFunctor G.toEnrichedFunctor k) :=
  BraidingComponents.generator_balanced d b F.toEnrichedFunctor G.toEnrichedFunctor k

example (k l : I) :
    MonoidalClosed.uncurry ((Output.functor d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor).map k l) ≫
        BraidingComponents.component d b F.toEnrichedFunctor G.toEnrichedFunctor l =
      (BraidingComponents.component d b F.toEnrichedFunctor G.toEnrichedFunctor k ⊗ₘ
        𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry ((Output.functor d.tensorEnrichedFunctor
          G.toEnrichedFunctor F.toEnrichedFunctor).map k l) :=
  BraidingFunctor.full_naturality d b F.toEnrichedFunctor G.toEnrichedFunctor k l

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    (β_ F G).hom ≫ (β_ G F).hom = 𝟙 (F ⊗ G) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  exact SymmetricCategory.symmetry F G

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    (α_ F G H).hom ≫ (β_ F (G ⊗ H)).hom ≫ (α_ G H F).hom =
      ((β_ F G).hom ▷ H) ≫ (α_ G F H).hom ≫ (G ◁ (β_ F H).hom) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  exact BraidedCategory.hexagon_forward F G H

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    (α_ F G H).inv ≫ (β_ (F ⊗ G) H).hom ≫ (α_ H F G).inv =
      (F ◁ (β_ G H).hom) ≫ (α_ F H G).inv ≫ ((β_ F H).hom ▷ G) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  exact BraidedCategory.hexagon_reverse F G H

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    (β_ (𝟙_ (EnrichedFunctorCat V I)) F).hom = (λ_ F).hom ≫ (ρ_ F).inv := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  exact CategoryTheory.braiding_tensorUnit_left F

include B

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    IsCommMonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.isCommMonObj d b S L B

example (k : I) (a : I × I) :
    gen d.tensorEnrichedFunctor S S k a ≫ BraidingComponents.component d b S S k ≫
        EnrichedFunctorCat.component (LaxMonoid.multiply d S L) k =
      gen d.tensorEnrichedFunctor S S k a ≫
        EnrichedFunctorCat.component (LaxMonoid.multiply d S L) k :=
  LaxMonoid.gen_multiply_braid d b S L B k a

example :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    (β_ (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom ≫
      MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I)) = MonObj.mul :=
  LaxMonoid.monObj_mul_comm d b S L B

end MathlibExtTest.EnrichedDayBraiding
