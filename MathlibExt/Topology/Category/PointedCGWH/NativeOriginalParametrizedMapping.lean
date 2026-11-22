/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.MappingParametrized
public import MathlibExt.Topology.Category.PointedCGWH.TensorMappingAdjunction

/-!
# Parametrized tensor–mapping adjunction for pointed spaces

For an index enriched in pointed compactly generated weak Hausdorff spaces,
the tensor and mapping bifunctors form a parametrized adjunction. The
construction uses the native tensor–mapping adjunctions, their Hom equivalences
and the projection naturality formula. At each fixed enriched functor, the
resulting adjunction is exactly the supplied native tensor–mapping adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeOriginalParametrizedMapping

open PointedCGWH.EnrichedFunctorMapping
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The actual tensor and mapping bifunctors use the canonical projection constructor. -/
def adjunction :
    (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := I)).flip ⊣₂
      WeightedEndVariance.bifunctor (V := PointedCGWH.{u, v}) (I := I) :=
  WeightedEndVariance.parametrizedOfProjection
    (fun X => tensorMappingAdjunction X) tensorHomEquiv
    tensorMappingAdjunction_homEquiv
    (fun X Y T f a => tensorHomEquiv_symm_π (X := X) (Y := Y) T f a)

/-- Each complete fixed adjunction is the supplied native tensor/mapping adjunction. -/
theorem fixed (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    adjunction.adj X = tensorMappingAdjunction X := rfl

end PointedCGWH.NativeOriginalParametrizedMapping
