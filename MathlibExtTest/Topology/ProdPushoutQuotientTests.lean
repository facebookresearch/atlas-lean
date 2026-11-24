/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutQuotient

@[expose] public section

/-!
# ProdPushout quotient client

Direct-import client for the fixed-left product/pushout quotient half:
comparison homeomorphism, its two value lemmas, and the quotient-descent
theorem. No general product/colimit claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat Topology

universe u

namespace MathlibExtTest.Topology.ProdPushoutQuotientTests

#check @TopCat.prodCoproductEmbed
#check @TopCat.prodCoproductEmbed_inl
#check @TopCat.prodCoproductEmbed_inr
#check @TopCat.isQuotientMap_coprodDesc_prodMap_of_isPushout

theorem prodPushout_quotient_client {K X₁ X₂ X₃ X₄ : TopCat.{u}}
    [LocallyCompactSpace ↑K] {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) :
    IsQuotientMap (coprod.desc (Limits.prod.map (𝟙 K) r)
      (Limits.prod.map (𝟙 K) b)) :=
  TopCat.isQuotientMap_coprodDesc_prodMap_of_isPushout h

#print axioms prodPushout_quotient_client
#print axioms TopCat.isQuotientMap_coprodDesc_prodMap_of_isPushout

end MathlibExtTest.Topology.ProdPushoutQuotientTests
