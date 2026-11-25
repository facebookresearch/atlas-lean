/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFactors

@[expose] public section

/-!
# ProdPushout factors client (KQ3)

Direct-import KQ3 client for the fixed-left product-pushout factorization:
restates `TopCat.prodPushoutFactors_of_isPushout` without unfolding it. No quotient,
fixed-right, DeltaGenerated, realization, or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.Category.TopCat.ProdPushoutFactorsTests

/-- Client restating the fixed-left product-pushout factorization. -/
theorem prodPushoutFactors_client {K X₁ X₂ X₃ X₄ : TopCat.{u}} [LocallyCompactSpace ↑K]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b)
    (s : PushoutCocone (Limits.prod.map (𝟙 K) t) (Limits.prod.map (𝟙 K) l)) :
    Function.FactorsThrough (coprod.desc s.inl s.inr)
      (coprod.desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b)) :=
  TopCat.prodPushoutFactors_of_isPushout h s

#print axioms prodPushoutFactors_client
#print axioms TopCat.prodPushoutFactors_of_isPushout

end MathlibExtTest.Topology.Category.TopCat.ProdPushoutFactorsTests
