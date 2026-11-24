/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberDesc
public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberFormula

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Factorization through the fixed-left product pushout quotient

Short composition of the pointwise descent and fiber formula helpers.
-/

/-- Factorization of the competing descent through the product quotient. -/
theorem prodPushoutFactors_of_isPushout
    {K X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b)
    (s : PushoutCocone (Limits.prod.map (𝟙 K) t) (Limits.prod.map (𝟙 K) l)) :
    Function.FactorsThrough (coprod.desc s.inl s.inr)
      (coprod.desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b)) := by
  choose D hD using fun k => TopCat.exists_prodMap_fiber_desc_of_isPushout h s k
  have hleft : ∀ (k : ↑K) (x : ↑X₂),
      D k (r x) = s.inl ((prodIsoProd K X₂).inv (k, x)) :=
    fun k x => (hD k).1 x
  have hright : ∀ (k : ↑K) (x : ↑X₃),
      D k (b x) = s.inr ((prodIsoProd K X₃).inv (k, x)) :=
    fun k x => (hD k).2 x
  intro p q hpq
  have e1 := TopCat.prodPushout_fiber_formula s D hleft hright p
  have e2 := TopCat.prodPushout_fiber_formula s D hleft hright q
  rw [e1, e2, hpq]

end TopCat
