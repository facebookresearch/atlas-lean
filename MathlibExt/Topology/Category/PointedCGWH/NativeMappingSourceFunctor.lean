/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCorner

/-!
# Contravariant native mapping-end functors

For a small enriched source and a fixed target diagram, the native mapping
end defines a contravariant functor in the source diagram. Native small
products and equalizers supply the mapping objects, and each source map is
the full weighted-end weight map. The object and whole map-family formulas
retain these chosen mapping ends and precomposition maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingSourceFunctor

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- The existing public native small-limit witness supplies source products. -/
theorem sourceHasProducts : HasProducts.{0} PointedCGWH.{u, v} := by
  infer_instance

/-- The existing public native small-limit witness supplies source equalizers. -/
theorem sourceHasEqualizers : HasEqualizers PointedCGWH.{u, v} := by
  infer_instance

/-- The existing native small-limit proof supplies the original object and relation products. -/
private theorem originalHasProducts : HasProducts.{0} PointedCGWH.{u, v} :=
  sourceHasProducts

/-- The same existing native small-limit proof supplies the original mapping equalizers. -/
private theorem originalHasEqualizers : HasEqualizers PointedCGWH.{u, v} :=
  sourceHasEqualizers


attribute [local instance] sourceHasProducts sourceHasEqualizers

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original full source-mapping functor, retaining actual end objects and input maps. -/
def source (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ ⥤ PointedCGWH.{u, v} :=
  WeightedEndVariance.bifunctor.flip.obj Z

/-- The complete original source functor is the original weighted-end bifunctor row. -/
theorem source_eq (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    source Z = WeightedEndVariance.bifunctor.flip.obj Z := rfl

/-- Every original source-functor object is its original chosen native mapping end. -/
theorem source_obj (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (source Z).obj (Opposite.op X) = PointedCGWH.EnrichedFunctorMapping.mappingObject X Z := rfl

/-- Every original source-functor map is the complete original enriched weight map. -/
theorem source_map (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (p : X ⟶ Y) :
    (source Z).map p.op = Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor
      Z.toEnrichedFunctor X.toEnrichedFunctor p := rfl

/-- The complete original source-functor arrow family retains both given maps. -/
theorem source_map_family (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (p : X ⟶ Y) => (source Z).map p.op) =
      (fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (p : X ⟶ Y) =>
        Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
          X.toEnrichedFunctor p) := rfl

end PointedCGWH.NativeMappingSourceFunctor
