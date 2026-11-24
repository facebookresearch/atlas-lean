/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorReconstructionBalance

/-!
# All-index original reverse operator Hom fields

The actual entire generator family descends through the tensor-preserved
original weighted coend. Its curried field retains every index and every
generator. The complete unit and composition laws subsequently assemble
these fields into the original operator-index enriched functor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory Opposite Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.Reconstruction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S X : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
  (X.externalTensor S) (d.tensorEnrichedFunctor.comp V X))
  (hU : IsSeparator (𝟙_ V))
  [∀ n k, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]
  [∀ n k, PreservesColimit (Discrete.functor (weightedCoend.relations (weight d n k) S))
    (tensorLeft (X.obj n))]
  [∀ n k, PreservesColimit (Discrete.functor (weightedCoend.objects (weight d n k) S))
    (tensorLeft (X.obj n))]
  [∀ n k, PreservesColimit
    (parallelPair (weightedCoend.leftMap (weight d n k) S)
      (weightedCoend.rightMap (weight d n k) S)) (tensorLeft (X.obj n))]

/-- The action uses the actual mapped original coend descent for every index pair. -/
def coendAction (n k : I) : X.obj n ⊗ Hom d S n k ⟶ X.obj k :=
  weightedCoend.Mapped.desc (weight d n k) S (tensorLeft (X.obj n))
    (generator d S X t n k) (generator_balanced d S X t hU n k)

/-- Its entire actual enriched Hom field is the curry of the same original descent. -/
def enrichedMapField (n k : I) : Hom d S n k ⟶ (ihom (X.obj n)).obj (X.obj k) :=
  MonoidalClosed.curry (coendAction d S X t hU n k)

/-- The whole map-field function retains the literal original supplier applications. -/
theorem enrichedMapField_eq_original_function :
    enrichedMapField d S X t hU =
      fun n k => MonoidalClosed.curry
        (weightedCoend.Mapped.desc (weight d n k) S (tensorLeft (X.obj n))
          (generator d S X t n k) (generator_balanced d S X t hU n k)) := rfl

/-- Every full original weighted-coend generator has its selected reconstructed value. -/
@[reassoc]
theorem gen_coendAction (n k a : I) :
    (X.obj n ◁ weightedCoend.ι (weight d n k) S a) ≫ coendAction d S X t hU n k =
      generator d S X t n k a :=
  weightedCoend.Mapped.gen_desc (weight d n k) S (tensorLeft (X.obj n))
    (generator d S X t n k) (generator_balanced d S X t hU n k) a

/-- Uncurrying the entire selected field gives the actual same coend action. -/
theorem uncurry_enrichedMapField (n k : I) :
    MonoidalClosed.uncurry (enrichedMapField d S X t hU n k) = coendAction d S X t hU n k :=
  MonoidalClosed.uncurry_curry (coendAction d S X t hU n k)

/-- All generators of the entire curried field retain their original reconstructed actions. -/
theorem gen_uncurry_enrichedMapField (n k a : I) :
    (X.obj n ◁ weightedCoend.ι (weight d n k) S a) ≫
        MonoidalClosed.uncurry (enrichedMapField d S X t hU n k) =
      generator d S X t n k a :=
  (congrArg (fun q => (X.obj n ◁ weightedCoend.ι (weight d n k) S a) ≫ q)
    (uncurry_enrichedMapField d S X t hU n k)).trans (gen_coendAction d S X t hU n k a)

end CategoryTheory.Enriched.SphereOperator.Reconstruction
