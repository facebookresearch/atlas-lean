/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeOriginalParametrizedMapping

/-!
# Characteristics of the parametrized tensor-mapping adjunction

Identifies the Hom equivalences, units and counits of the parametrized adjunction with
the tensor/weighted-end adjunction. Projection and component formulas express its maps
through the braiding and end evaluation, and retain both triangle identities.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory EnrichedFunctorCat MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.NativeParametrizedCharacteristics

open PointedCGWH.EnrichedFunctorMapping
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- Every original parametrized fixed Hom equivalence is the original native tensor/end inverse. -/
theorem homEquiv (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (T : PointedCGWH.{u, v}) :
    (NativeOriginalParametrizedMapping.adjunction.adj X).homEquiv T Y =
      (tensorHomEquiv X Y T).symm := by
  rw [NativeOriginalParametrizedMapping.fixed]
  exact tensorMappingAdjunction_homEquiv X Y T

/-- The complete original parametrized unit transformation is unchanged. -/
theorem unit (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (NativeOriginalParametrizedMapping.adjunction.adj X).unit =
      (tensorMappingAdjunction X).unit :=
  congrArg (fun adj => adj.unit) (NativeOriginalParametrizedMapping.fixed X)

/-- The complete original parametrized counit transformation is unchanged. -/
theorem counit (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (NativeOriginalParametrizedMapping.adjunction.adj X).counit =
      (tensorMappingAdjunction X).counit :=
  congrArg (fun adj => adj.counit) (NativeOriginalParametrizedMapping.fixed X)

/-- Every actual unit projection is the original inverse ambient braid under currying. -/
theorem unit_projection (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (T : PointedCGWH.{u, v}) (a : I) :
    (NativeOriginalParametrizedMapping.adjunction.adj X).unit.app T ≫
      π X (tensorLeftObject T X) a =
      MonoidalClosed.curry ((β_ T (X.toEnrichedFunctor.obj a)).inv) := by
  rw [unit]
  exact tensorMappingAdjunction_unit_π X T a

/-- Every actual counit component is the same full original end evaluation. -/
theorem counit_component (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component ((NativeOriginalParametrizedMapping.adjunction.adj X).counit.app Y) a =
      (β_ (mappingObject X Y) (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (π X Y a) := by
  rw [counit]
  exact tensorMappingAdjunction_counit_component X Y a

/-- The full original parametrized unit and counit retain the actual left triangle. -/
theorem left_triangle (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (T : PointedCGWH.{u, v}) :
    scalarTensorMap ((NativeOriginalParametrizedMapping.adjunction.adj X).unit.app T) X ≫
        (NativeOriginalParametrizedMapping.adjunction.adj X).counit.app
          (tensorLeftObject T X) = 𝟙 (tensorLeftObject T X) := by
  rw [unit, counit]
  exact tensorMappingAdjunction_left_triangle X T

/-- The full original parametrized unit and counit retain the actual right triangle. -/
theorem right_triangle (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (NativeOriginalParametrizedMapping.adjunction.adj X).unit.app (mappingObject X Y) ≫
      WeightedEndVariance.post X
        ((NativeOriginalParametrizedMapping.adjunction.adj X).counit.app Y) =
      𝟙 (mappingObject X Y) := by
  rw [unit, counit]
  exact tensorMappingAdjunction_right_triangle X Y

end PointedCGWH.NativeParametrizedCharacteristics
