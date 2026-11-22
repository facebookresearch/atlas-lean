/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingProofFamilyTransport
public import MathlibExt.CategoryTheory.Enriched.WeightedEndSourceTransport

/-!
# Preservation by the literal native source mapping functor

The whole original source functor equality and the actual original
parametrized tensor/end adjunction first use explicit end proof witnesses.
Their preservation proofs are transported as complete families. The final
client discharges the witnesses with the existing native small limits.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingSourcePreservation

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The literal source functor has all source-limit preservation
after its whole original end-proof families are fixed explicitly. -/
theorem source_preservesLimitsOfSize_to_given
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v})
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesLimitsOfSize.{w, w'} (NativeMappingSourceFunctor.source E) :=
  @WeightedEndSourceTransport.source_preservesLimitsOfSize PointedCGWH.{u, v} _ _ _ _
    I _ hp he (NativeMappingProofFamilyTransport.originalAdjunctionToGiven hp he)
    (fun E => NativeMappingSourceFunctor.source E)
    (NativeMappingProofFamilyTransport.source_function_to_given hp he) E

/-- The literal original source functor preserves all source limits.
Both existence witnesses come from the actual native small-limit proof. -/
theorem source_preservesLimitsOfSize (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesLimitsOfSize.{w, w'} (NativeMappingSourceFunctor.source E) :=
  source_preservesLimitsOfSize_to_given (by infer_instance) (by infer_instance) E

/-- The literal original source functor preserves all small limits. -/
theorem source_preservesLimits (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesLimits (NativeMappingSourceFunctor.source E) := source_preservesLimitsOfSize E

end PointedCGWH.NativeMappingSourcePreservation
