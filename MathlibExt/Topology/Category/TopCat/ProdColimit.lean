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
# Colimit preservation by products in `TopCat`

For a locally compact space `K : TopCat.{u}`, the fixed-left product
functor preserves all `u`-small colimits. The result combines preservation
of coproducts and coequalizers; local compactness is required on the
fixed factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

variable (K : TopCat.{u}) [LocallyCompactSpace (↑K : Type u)]

/-- Fixed-left product with a locally compact factor `K` preserves all `u`-small
colimits. -/
instance preservesColimits_prodFunctorObj :
    PreservesColimitsOfSize.{u, u} (Limits.prod.functor.obj K) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts _

end TopCat
