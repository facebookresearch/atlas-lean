/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Enriched.SphereOperatorFunctorActions
import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexUnitFunctor

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.SourcePrerequisiteOwner

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

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    weightedCoend.Mapped.Balanced (weight d n k) S
      (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)) (generatorAction d S L F n k) :=
  generatorAction_balanced d S L F n k

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁
      ((λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon))) ≫
        generatorAction d S L F n n (𝟙_ I) =
      (ρ_ (F.toEnrichedFunctor.obj ⟨n⟩)).hom :=
  generatorAction_unit d S L F n

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k l a b : I) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁ compositionGenerator d S L n k l a b) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩) =
      (α_ (F.toEnrichedFunctor.obj ⟨n⟩)
        (weightedCoend.objects (weight d n k) S a)
        (weightedCoend.objects (weight d k l) S b)).inv ≫
          (generatorAction d S L F n k a ▷ weightedCoend.objects (weight d k l) S b) ≫
            generatorAction d S L F k l b :=
  generatorAction_comp d S L F n k l a b

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    MonoidalClosed.curry
      (weightedCoend.Mapped.desc (weight d n k) S
        (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)) (generatorAction d S L F n k)
        (generatorAction_balanced d S L F n k)) = F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ :=
  generatorAction_reconstruct d S L F n k

example (n k l : I) :
    eComp V n k l ≫ indexHom d S L n l =
      (indexHom d S L n k ⊗ₘ indexHom d S L k l) ≫ composition d S L n k l :=
  indexHom_comp d S L n k l

example (n : I) :
    eId V n ≫ indexHom d S L n n = identityGenerator d S L n :=
  indexHom_id d S L n

example {n k : I} (f : n ⟶ k) :
    eHomEquiv V f ≫ indexHom d S L n k =
      (λ_ (𝟙_ V)).inv ≫
        (eHomEquiv V ((λ_ n).hom ≫ f) ⊗ₘ L.epsilon) ≫
          weightedCoend.ι (weight d n k) S (𝟙_ I) :=
  indexHom_point d S L f

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    ((indexRestriction d S L).obj F).toEnrichedFunctor.map n k =
      indexHom d S L n k ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ :=
  indexRestriction_fullMap d S L F n k

example (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k l : I) :
    eComp V n k l ≫ ((indexRestriction d S L).obj F).toEnrichedFunctor.map n l =
      (((indexRestriction d S L).obj F).toEnrichedFunctor.map n k ⊗ₘ
        ((indexRestriction d S L).obj F).toEnrichedFunctor.map k l) ≫
          eComp V (F.toEnrichedFunctor.obj ⟨n⟩) (F.toEnrichedFunctor.obj ⟨k⟩)
            (F.toEnrichedFunctor.obj ⟨l⟩) :=
  ((indexRestriction d S L).obj F).toEnrichedFunctor.map_comp n k l

example (F G : EnrichedFunctorCat V (OperatorIndex d S L)) (α : F ⟶ G) (n : I) :
    EnrichedFunctorCat.component ((indexRestriction d S L).map α) n =
      EnrichedFunctorCat.component α ⟨n⟩ :=
  EnrichedFunctorCat.restrictionMap_component (indexUnitFunctor d S L) α n

end CategoryTheory.Enriched.SphereOperator.SourcePrerequisiteOwner
