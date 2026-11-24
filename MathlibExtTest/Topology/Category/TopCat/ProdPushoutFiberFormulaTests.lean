/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberFormula

@[expose] public section

/-!
# ProdPushout fiber formula client (KQ3)

Direct-import KQ3 client for the fixed-left product-pushout fiber formula:
restates `TopCat.prodPushout_fiber_formula` without unfolding it. No quotient,
fixed-right, DeltaGenerated, realization, or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.Category.TopCat.ProdPushoutFiberFormulaTests

/-- Client restating the fixed-left product-pushout fiber formula. -/
theorem prodPushout_fiber_formula_client {K X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (s : PushoutCocone (Limits.prod.map (𝟙 K : K ⟶ K) t)
      (Limits.prod.map (𝟙 K : K ⟶ K) l))
    (D : ↑K → ↑X₄ → ↑s.pt)
    (hleft : ∀ k x₂, D k (r x₂) = s.inl ((prodIsoProd K X₂).inv (k, x₂)))
    (hright : ∀ k x₃, D k (b x₃) = s.inr ((prodIsoProd K X₃).inv (k, x₃)))
    (z : ↑((K ⨯ X₂) ⨿ (K ⨯ X₃))) :
    (coprod.desc s.inl s.inr) z =
      D ((Limits.prod.fst : K ⨯ X₄ ⟶ K)
        ((coprod.desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
          (Limits.prod.map (𝟙 K : K ⟶ K) b)) z))
        ((Limits.prod.snd : K ⨯ X₄ ⟶ X₄)
          ((coprod.desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
            (Limits.prod.map (𝟙 K : K ⟶ K) b)) z)) :=
  TopCat.prodPushout_fiber_formula s D hleft hright z

#print axioms prodPushout_fiber_formula_client
#print axioms TopCat.prodPushout_fiber_formula

end MathlibExtTest.Topology.Category.TopCat.ProdPushoutFiberFormulaTests
