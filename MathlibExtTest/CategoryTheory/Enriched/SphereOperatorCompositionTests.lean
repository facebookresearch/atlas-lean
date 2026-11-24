/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

namespace SphereOperatorCompositionTests

open CategoryTheory CategoryTheory.Enriched MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

#check @SphereOperator.indexGenerator.{0, 0, 0, 0}
#check @SphereOperator.indexGenerator.{1, 0, 0, 1}
#check @SphereOperator.indexGenerator.{0, 1, 1, 0}
#check @SphereOperator.indexGenerator.{1, 1, 1, 1}
#check @SphereOperator.compositionGenerator.{0, 0, 0, 0}
#check @SphereOperator.compositionGenerator.{1, 0, 0, 1}
#check @SphereOperator.compositionGenerator.{0, 1, 1, 0}
#check @SphereOperator.compositionGenerator.{1, 1, 1, 1}

example (d : EnrichedMonoidalCategoryData V I) (n k l a b : I) :
    SphereOperator.indexGenerator d n k l a b =
      ((((λ_ ((a ⊗ n) ⟶[V] k)).inv ≫
          (eId V b ⊗ₘ 𝟙 ((a ⊗ n) ⟶[V] k)) ≫
            d.tensorMap b b (a ⊗ n) k) ⊗ₘ 𝟙 ((b ⊗ k) ⟶[V] l)) ≫
        eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
        (λ_ ((b ⊗ (a ⊗ n)) ⟶[V] l)).inv ≫
        (eHomEquiv V (α_ b a n).hom ⊗ₘ
          𝟙 ((b ⊗ (a ⊗ n)) ⟶[V] l)) ≫
        eComp V ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n)) l := rfl

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n k l a b : I)
  [HasCoproduct (weightedCoend.relations (SphereOperator.weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (SphereOperator.weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (SphereOperator.weight d n l) S)
    (weightedCoend.rightMap (SphereOperator.weight d n l) S)]

example :
    SphereOperator.compositionGenerator d S L n k l a b =
      MonoidalCategory.tensorδ ((a ⊗ n) ⟶[V] k) ((b ⊗ k) ⟶[V] l)
          (S.obj a) (S.obj b) ≫
        ((𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b ⊗ k) ⟶[V] l))) ⊗ₘ
          (β_ (S.obj a) (S.obj b)).hom) ≫
        (SphereOperator.indexGenerator d n k l a b ⊗ₘ L.mu b a) ≫
        weightedCoend.ι (SphereOperator.weight d n l) S (b ⊗ a) := rfl


-- A distinct comparison client: base symmetry recovers the original full map.
-- The generic construction above has no symmetry hypothesis on its base or index.
section SymmetricBaseCompatibility

variable {V' : Type uV} [Category.{vV} V'] [MonoidalCategory V']
  [SymmetricCategory V'] [MonoidalClosed V']
  {I' : Type uI} [Category.{vI} I'] [MonoidalCategory I']
  [EnrichedOrdinaryCategory V' I']

example (d' : EnrichedMonoidalCategoryData V' I') (S' : EnrichedFunctor V' I' V')
    (L' : EnrichedFunctor.LaxMonoidalData d'
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V') S')
    (n' k' l' a' b' : I')
    [HasCoproduct (weightedCoend.relations (SphereOperator.weight d' n' l') S')]
    [HasCoproduct (weightedCoend.objects (SphereOperator.weight d' n' l') S')]
    [HasCoequalizer (weightedCoend.leftMap (SphereOperator.weight d' n' l') S')
      (weightedCoend.rightMap (SphereOperator.weight d' n' l') S')] :
    SphereOperator.compositionGenerator d' S' L' n' k' l' a' b' =
      MonoidalCategory.tensorμ ((a' ⊗ n') ⟶[V'] k') (S'.obj a')
          ((b' ⊗ k') ⟶[V'] l') (S'.obj b') ≫
        ((𝟙 (((a' ⊗ n') ⟶[V'] k') ⊗ ((b' ⊗ k') ⟶[V'] l'))) ⊗ₘ
          (β_ (S'.obj a') (S'.obj b')).hom) ≫
        (SphereOperator.indexGenerator d' n' k' l' a' b' ⊗ₘ L'.mu b' a') ≫
        weightedCoend.ι (SphereOperator.weight d' n' l') S' (b' ⊗ a') := by
  dsimp only [SphereOperator.compositionGenerator, MonoidalCategory.tensorδ,
    MonoidalCategory.tensorμ]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding
    ((b' ⊗ k') ⟶[V'] l') (S'.obj a')]

end SymmetricBaseCompatibility

#print axioms SphereOperator.indexGenerator
#print axioms SphereOperator.compositionGenerator

-- Original two-generator and native symmetric compatibility clients above remain byte-identical.
-- These clients use the new exposed full two-coend map under the original three particular coend choices.
section ActualTwoCoendComposition

variable [HasCoproduct (weightedCoend.relations (SphereOperator.weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (SphereOperator.weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (SphereOperator.weight d n k) S)
    (weightedCoend.rightMap (SphereOperator.weight d n k) S)]
  [HasCoproduct (weightedCoend.relations (SphereOperator.weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (SphereOperator.weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (SphereOperator.weight d k l) S)
    (weightedCoend.rightMap (SphereOperator.weight d k l) S)]

#check @SphereOperator.composition.{0, 0, 0, 0}
#check @SphereOperator.composition.{1, 0, 0, 1}
#check @SphereOperator.composition.{0, 1, 1, 0}
#check @SphereOperator.composition.{1, 1, 1, 1}
#check @SphereOperator.composition_generator.{0, 0, 0, 0}
#check @SphereOperator.composition_generator.{1, 0, 0, 1}
#check @SphereOperator.composition_generator.{0, 1, 1, 0}
#check @SphereOperator.composition_generator.{1, 1, 1, 1}

example : SphereOperator.Hom d S n k ⊗ SphereOperator.Hom d S k l ⟶
    SphereOperator.Hom d S n l := SphereOperator.composition d S L n k l

example :
    (weightedCoend.ι (SphereOperator.weight d n k) S a ⊗ₘ
      weightedCoend.ι (SphereOperator.weight d k l) S b) ≫
        SphereOperator.composition d S L n k l =
      SphereOperator.compositionGenerator d S L n k l a b := by
  exact SphereOperator.composition_generator d S L n k l a b

end ActualTwoCoendComposition

#print axioms SphereOperator.composition
#print axioms SphereOperator.composition_generator

end SphereOperatorCompositionTests
