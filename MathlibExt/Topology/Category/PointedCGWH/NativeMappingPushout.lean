/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourcePreservation

/-!
# The actual native source pushout is a full mapping pullback

Every source object and every pushout map is the caller's original one.
The actual native source preservation supplier carries the same chosen
pushout to a pullback. The original weighted-end projection maps retain
the two quotient legs and both original compatibility legs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingPushout

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The entire original source functor sends the caller's same
pushout to an actual pullback, with all four original map functions. -/
theorem sourceFunctorSquare
    {A B Z C : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ B) (z : A ⟶ Z) (kB : B ⟶ C) (kZ : Z ⟶ C)
    (sq : IsPushout i z kB kZ) (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPullback ((NativeMappingSourceFunctor.source E).map kB.op)
      ((NativeMappingSourceFunctor.source E).map kZ.op)
      ((NativeMappingSourceFunctor.source E).map i.op)
      ((NativeMappingSourceFunctor.source E).map z.op) := by
  let _ : PreservesLimits (NativeMappingSourceFunctor.source E) :=
    NativeMappingSourcePreservation.source_preservesLimits E
  exact (sq.op.map (NativeMappingSourceFunctor.source E)).flip

/-- With the same original end proof families explicit, the actual
native weighted-end square keeps every original caller pushout map. -/
theorem sourceSquare_to_given
    (hp : HasProducts.{0} PointedCGWH.{u, v}) (he : HasEqualizers PointedCGWH.{u, v})
    {A B Z C : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ B) (z : A ⟶ Z) (kB : B ⟶ C) (kZ : Z ⟶ C)
    (sq : IsPushout i z kB kZ) (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPullback
      (@WeightedEndVariance.pre PointedCGWH.{u, v} _ _ _ _ I _ hp he C B kB E)
      (@WeightedEndVariance.pre PointedCGWH.{u, v} _ _ _ _ I _ hp he C Z kZ E)
      (@WeightedEndVariance.pre PointedCGWH.{u, v} _ _ _ _ I _ hp he B A i E)
      (@WeightedEndVariance.pre PointedCGWH.{u, v} _ _ _ _ I _ hp he Z A z E) :=
  @WeightedEndSourceLimits.sourceSquare PointedCGWH.{u, v} _ _ _ _ I _ hp he
    (NativeMappingProofFamilyTransport.originalAdjunctionToGiven hp he)
    A B Z C i z kB kZ sq E

/-- The original native small limits discharge all end-existence
witnesses for the actual whole source mapping pullback. -/
theorem sourceSquare
    {A B Z C : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ B) (z : A ⟶ Z) (kB : B ⟶ C) (kZ : Z ⟶ C)
    (sq : IsPushout i z kB kZ) (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPullback (WeightedEndVariance.pre kB E) (WeightedEndVariance.pre kZ E)
      (WeightedEndVariance.pre i E) (WeightedEndVariance.pre z E) :=
  sourceSquare_to_given (by infer_instance) (by infer_instance) i z kB kZ sq E

end PointedCGWH.NativeMappingPushout
