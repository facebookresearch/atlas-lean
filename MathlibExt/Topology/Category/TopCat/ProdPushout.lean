/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFactors
public import MathlibExt.Topology.Category.TopCat.ProdPushoutQuotient

/-!
# Fixed-left product preserves TopCat pushouts

Short-stack assembly of the quotient and factorization halves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-- Fixed-left product preserves TopCat pushouts. -/
theorem isPushout_prodMap_left_of_isPushout
    {K X₁ X₂ X₃ X₄ : TopCat.{u}} [LocallyCompactSpace ↑K]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b) :
    IsPushout (prod.map (𝟙 K) t) (prod.map (𝟙 K) l)
      (prod.map (𝟙 K) r) (prod.map (𝟙 K) b) := by
  have hcomm : t ≫ r = l ≫ b := h.w
  have hcommProd : prod.map (𝟙 K) t ≫ prod.map (𝟙 K) r =
      prod.map (𝟙 K) l ≫ prod.map (𝟙 K) b := by
    rw [Limits.prod.map_map, Limits.prod.map_map, hcomm]
  have hq := TopCat.isQuotientMap_coprodDesc_prodMap_of_isPushout (K := K) h
  have hfac := TopCat.prodPushoutFactors_of_isPushout (K := K) h
  have hcolim :=
    TopCat.pushoutCoconeIsColimitOfIsQuotientMap
      (PushoutCocone.mk (prod.map (𝟙 K) r) (prod.map (𝟙 K) b) hcommProd) hq hfac
  exact IsPushout.of_isColimit hcolim

end TopCat
