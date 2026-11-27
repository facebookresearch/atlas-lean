/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorFunctorActions

/-!
# Genuine operator transformations from all original generator actions

Full coefficient-generator naturality characterizes the entire enriched
Hom naturality square. Every actual native Hom and sphere coefficient is
retained. The resulting genuine unit-graded transformation uses the given
component maps, without a separator or a supplied full naturality law.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- Every actual generator square determines the whole original enriched action square. -/
theorem fullNaturality_of_generatorNaturality
    (F G : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I)
    (qN : F.toEnrichedFunctor.obj ⟨n⟩ ⟶ G.toEnrichedFunctor.obj ⟨n⟩)
    (qK : F.toEnrichedFunctor.obj ⟨k⟩ ⟶ G.toEnrichedFunctor.obj ⟨k⟩)
    (h : ∀ a : I,
      generatorAction d S L F n k a ≫ qK =
        (qN ▷ weightedCoend.objects (weight d n k) S a) ≫
          generatorAction d S L G n k a) :
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) ≫ qK =
      (qN ▷ Hom d S n k) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) := by
  apply weightedCoend.Mapped.hom_ext (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
  intro a
  let X : V := F.toEnrichedFunctor.obj ⟨n⟩
  let Y : V := G.toEnrichedFunctor.obj ⟨n⟩
  let P : V := weightedCoend.objects (weight d n k) S a
  let H : V := Hom d S n k
  let i : P ⟶ H := weightedCoend.ι (weight d n k) S a
  let f : X ⊗ H ⟶ F.toEnrichedFunctor.obj ⟨k⟩ :=
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  let g : Y ⊗ H ⟶ G.toEnrichedFunctor.obj ⟨k⟩ :=
    MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)
  have hF : generatorAction d S L F n k a = X ◁ i ≫ f := rfl
  have hG : generatorAction d S L G n k a = Y ◁ i ≫ g := rfl
  change (X ◁ i) ≫ (f ≫ qK) = (X ◁ i) ≫ ((qN ▷ H) ≫ g)
  calc
    _ = ((X ◁ i) ≫ f) ≫ qK := (Category.assoc (X ◁ i) f qK).symm
    _ = generatorAction d S L F n k a ≫ qK := congrArg (fun z => z ≫ qK) hF.symm
    _ = (qN ▷ P) ≫ generatorAction d S L G n k a := h a
    _ = (qN ▷ P) ≫ ((Y ◁ i) ≫ g) := congrArg (fun z => (qN ▷ P) ≫ z) hG
    _ = ((qN ▷ P) ≫ (Y ◁ i)) ≫ g := (Category.assoc (qN ▷ P) (Y ◁ i) g).symm
    _ = ((X ◁ i) ≫ (qN ▷ H)) ≫ g :=
      congrArg (fun z => z ≫ g) (whisker_exchange qN i).symm
    _ = _ := Category.assoc (X ◁ i) (qN ▷ H) g

/-- The whole original action square implies every original generator square. -/
theorem generatorNaturality_of_fullNaturality
    (F G : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I)
    (qN : F.toEnrichedFunctor.obj ⟨n⟩ ⟶ G.toEnrichedFunctor.obj ⟨n⟩)
    (qK : F.toEnrichedFunctor.obj ⟨k⟩ ⟶ G.toEnrichedFunctor.obj ⟨k⟩)
    (h : MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) ≫ qK =
      (qN ▷ Hom d S n k) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩))
    (a : I) :
    generatorAction d S L F n k a ≫ qK =
      (qN ▷ weightedCoend.objects (weight d n k) S a) ≫
        generatorAction d S L G n k a := by
  let i := weightedCoend.ι (weight d n k) S a
  have hi := congrArg (fun z => (F.toEnrichedFunctor.obj ⟨n⟩ ◁ i) ≫ z) h
  change ((F.toEnrichedFunctor.obj ⟨n⟩ ◁ i) ≫
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)) ≫ qK = _
  rw [Category.assoc]
  rw [hi, ← Category.assoc, whisker_exchange, Category.assoc]
  rfl

/-- The complete generator squares construct a genuine full unit-graded transformation. -/
def transformationOfGeneratorNaturality
    (F G : EnrichedFunctorCat V (OperatorIndex d S L))
    (q : ∀ n : OperatorIndex d S L, F.toEnrichedFunctor.obj n ⟶ G.toEnrichedFunctor.obj n)
    (h : ∀ n k a : I,
      generatorAction d S L F n k a ≫ q ⟨k⟩ =
        (q ⟨n⟩ ▷ weightedCoend.objects (weight d n k) S a) ≫
          generatorAction d S L G n k a) : F ⟶ G :=
  GradedNatTrans.unitOfComponents q (by
    intro n k
    rcases n with ⟨n⟩
    rcases k with ⟨k⟩
    rw [tensorHom_id]
    exact fullNaturality_of_generatorNaturality d S L F G n k (q ⟨n⟩) (q ⟨k⟩) (h n k))

/-- Every component of the reconstructed whole transformation is the original supplied map. -/
theorem transformationOfGeneratorNaturality_component
    (F G : EnrichedFunctorCat V (OperatorIndex d S L))
    (q : ∀ n : OperatorIndex d S L, F.toEnrichedFunctor.obj n ⟶ G.toEnrichedFunctor.obj n)
    (h : ∀ n k a : I,
      generatorAction d S L F n k a ≫ q ⟨k⟩ =
        (q ⟨n⟩ ▷ weightedCoend.objects (weight d n k) S a) ≫
          generatorAction d S L G n k a) (n : OperatorIndex d S L) :
    EnrichedFunctorCat.component (transformationOfGeneratorNaturality d S L F G q h) n = q n :=
  GradedNatTrans.unitOfComponents_component _ _ n

/-- All actual coefficient-generator actions determine the full original operator Hom map. -/
theorem fullAction_eq_of_generators
    (F G : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k : I) (hN : F.toEnrichedFunctor.obj ⟨n⟩ = G.toEnrichedFunctor.obj ⟨n⟩)
    (hK : F.toEnrichedFunctor.obj ⟨k⟩ = G.toEnrichedFunctor.obj ⟨k⟩)
    (h : ∀ a : I,
      generatorAction d S L F n k a ≫ eqToHom hK =
        (eqToHom hN ▷ weightedCoend.objects (weight d n k) S a) ≫
          generatorAction d S L G n k a) :
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) ≫ eqToHom hK =
      (eqToHom hN ▷ Hom d S n k) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) :=
  fullNaturality_of_generatorNaturality d S L F G n k (eqToHom hN) (eqToHom hK) h

end CategoryTheory.Enriched.SphereOperator
