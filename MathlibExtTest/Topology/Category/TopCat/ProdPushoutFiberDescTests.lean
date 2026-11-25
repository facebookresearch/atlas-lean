/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberDesc

@[expose] public section

/-!
# ProdPushout fiber descent client (KQ3)

Direct-import KQ3 client for the fixed-left product pushout single-fiber
descent: restates `TopCat.exists_prodMap_fiber_desc_of_isPushout` without
unfolding it. No quotient, fixed-right, DeltaGenerated, realization, or
model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.Category.TopCat.ProdPushoutFiberDescTests

/-- Client restating single-fiber descent along a fixed-left product pushout. -/
theorem prodPushout_fiber_desc_client {K X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b)
    (s : PushoutCocone (Limits.prod.map (𝟙 K) t) (Limits.prod.map (𝟙 K) l))
    (k : ↑K) :
    ∃ (d : ↑X₄ → ↑s.pt),
      (∀ x : ↑X₂, d (r x) = s.inl ((prodIsoProd K X₂).inv (k, x))) ∧
      (∀ x : ↑X₃, d (b x) = s.inr ((prodIsoProd K X₃).inv (k, x))) :=
  TopCat.exists_prodMap_fiber_desc_of_isPushout h s k

#print axioms prodPushout_fiber_desc_client
#print axioms TopCat.exists_prodMap_fiber_desc_of_isPushout

end MathlibExtTest.Topology.Category.TopCat.ProdPushoutFiberDescTests
