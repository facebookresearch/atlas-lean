/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEndProofFamilies
public import MathlibExt.CategoryTheory.Enriched.WeightedEndSourceLimits
public import MathlibExt.CategoryTheory.Adjunction.Parametrized.WholeRecovery
public import MathlibExt.Topology.Category.PointedCGWH.NativeOriginalParametrizedMapping
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourceFunctor

/-!
# Whole original native source functions under their end proof families

The complete actual source functor is transported through the original
weighted-end proof-family equalities. Category, monoidal, braided, closed
and enriched data remain the same original native values throughout.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingProofFamilyTransport

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The entire original source functor agrees with the same original
weighted-end algorithm under any given global existence witnesses. -/
theorem source_function_to_given
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v}) :
    (fun E : EnrichedFunctorCat PointedCGWH.{u, v} I => NativeMappingSourceFunctor.source E) =
      fun E : EnrichedFunctorCat PointedCGWH.{u, v} I =>
        (@WeightedEndVariance.bifunctor PointedCGWH.{u, v} _ _ _ _ I _ hp he).flip.obj E := by
  unfold NativeMappingSourceFunctor.source
  exact Enriched.WeightedEndProofFamilies.source_functor_function_eq _ hp _ he

/-- The entire original native parametrized adjunction is transported
through equality of its global end-existence proof families. -/
def originalAdjunctionToGiven
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v}) :
    WeightedEndVariance.tensorBifunctor.flip ⊣₂
      @WeightedEndVariance.bifunctor PointedCGWH.{u, v} _ _ _ _ I _ hp he :=
  ParametrizedAdjunction.transportWhole rfl
    (Enriched.WeightedEndProofFamilies.bifunctor_proof_eq _ hp _ he)
    NativeOriginalParametrizedMapping.adjunction

/-- This is the same complete original native adjunction value, with
all source, target, coefficient, unit and counit data transported. -/
theorem originalAdjunctionToGiven_heq
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v}) :
    HEq (originalAdjunctionToGiven (I := I) hp he)
      (NativeOriginalParametrizedMapping.adjunction (I := I)) := by
  unfold originalAdjunctionToGiven
  exact ParametrizedAdjunction.transportWhole_heq _ _ _

/-- Under the given end witnesses, actual native tensor/cotensor
adjunctions prove preservation of source limits at every shape size. -/
theorem weighted_source_preservesLimitsOfSize
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v})
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesLimitsOfSize.{w, w'}
      ((@WeightedEndVariance.bifunctor PointedCGWH.{u, v} _ _ _ _ I _ hp he).flip.obj E) :=
  @WeightedEndSourceLimits.source_preservesLimitsOfSize PointedCGWH.{u, v} _ _ _ _
    I _ hp he (originalAdjunctionToGiven hp he) E

end PointedCGWH.NativeMappingProofFamilyTransport
