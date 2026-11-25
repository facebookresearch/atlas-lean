/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutSymm

@[expose] public section

/-!
# ProdPushout symmetry client (KQ3)

Direct-import KQ3 client for the fixed-right product pushout symmetry adapter:
restates `TopCat.isPushout_prod_map_fixedRight_of_fixedLeft` without unfolding
it. No preservation, quotient, DeltaGenerated, realization, or model-category
claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.Category.TopCat.ProdPushoutSymmTests

/-- Client restating fixed-right pushout from a fixed-left product pushout. -/
theorem prodPushout_symm_client {Z X Y X' Y' : TopCat.{u}}
    {f : X ⟶ Y} {g : X ⟶ X'} {inl : Y ⟶ Y'} {inr : X' ⟶ Y'}
    (hL : IsPushout
      (prod.map (𝟙 Z) f) (prod.map (𝟙 Z) g)
      (prod.map (𝟙 Z) inl) (prod.map (𝟙 Z) inr)) :
    IsPushout
      (prod.map f (𝟙 Z)) (prod.map g (𝟙 Z))
      (prod.map inl (𝟙 Z)) (prod.map inr (𝟙 Z)) :=
  TopCat.isPushout_prod_map_fixedRight_of_fixedLeft hL

#print axioms prodPushout_symm_client
#print axioms TopCat.isPushout_prod_map_fixedRight_of_fixedLeft

end MathlibExtTest.Topology.Category.TopCat.ProdPushoutSymmTests
