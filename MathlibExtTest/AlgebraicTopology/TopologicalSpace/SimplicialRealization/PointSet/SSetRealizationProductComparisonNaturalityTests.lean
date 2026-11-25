/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationProductComparisonNaturality

@[expose] public section

open CategoryTheory

universe u v

/-!
# Product-comparison naturality client test

KQ3 only. Direct client application of
`SSet.prodComparison_toTop_natural_apply` with all object, map, and point
arguments explicit. No inverse, injectivity, boundary, colimit, or
model-category content.
-/

namespace SSet

/-- Direct client application of product-comparison naturality. -/
theorem prodComparison_toTop_natural_apply_client
    {X Y X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : ↑(SSet.toTop.obj (X ⨯ Y))) :
    (Limits.prodComparison SSet.toTop X' Y')
        ((SSet.toTop.map (Limits.prod.map f g)) p) =
      (Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g))
        ((Limits.prodComparison SSet.toTop X Y) p) :=
  SSet.prodComparison_toTop_natural_apply f g p

/-- Explicit `Type 1` client for the universe-polymorphic theorem. -/
example {X Y X' Y' : SSet.{1}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : ↑(SSet.toTop.obj (X ⨯ Y))) :
    (Limits.prodComparison SSet.toTop X' Y')
        ((SSet.toTop.map (Limits.prod.map f g)) p) =
      (Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g))
        ((Limits.prodComparison SSet.toTop X Y) p) :=
  SSet.prodComparison_toTop_natural_apply f g p

/-- Client in a common `max u v` universe, as used when independently
universe-parameterized inputs are placed in one simplicial-set category. -/
example {X Y X' Y' : SSet.{max u v}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : ↑(SSet.toTop.obj (X ⨯ Y))) :
    (Limits.prodComparison SSet.toTop X' Y')
        ((SSet.toTop.map (Limits.prod.map f g)) p) =
      (Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g))
        ((Limits.prodComparison SSet.toTop X Y) p) :=
  SSet.prodComparison_toTop_natural_apply f g p

#print axioms SSet.prodComparison_toTop_natural_apply
#print axioms SSet.prodComparison_toTop_natural_apply_client

end SSet
