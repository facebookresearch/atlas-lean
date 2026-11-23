/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdCoproduct
public import MathlibExt.Topology.Category.TopCat.ProdCoequalizer
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Locally compact products and topological colimits

Cartesian product with a fixed locally compact topological space preserves
small colimits in TopCat. The preservation instance is obtained from the
corresponding coproduct and coequalizer preservation results.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

variable (K : TopCat.{u}) [LocallyCompactSpace (↑K : Type u)]

/-- Fixed-left TopCat product with a locally compact left factor preserves all `u`-small
colimits. Requires `[LocallyCompactSpace (↑K : Type u)]` on the fixed left factor `K`.
This proves no arbitrary-left-factor result and carries no model-category claim. -/
instance preservesColimits_prodFunctorObj :
    PreservesColimitsOfSize.{u, u} (Limits.prod.functor.obj K) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts _

end TopCat
