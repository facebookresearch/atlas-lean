/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberDesc
public import MathlibExt.Topology.Category.TopCat.ProdPushoutFiberFormula

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Constancy on fixed-left product descent fibers

For a pushout X₁→X₂,X₃→X₄ and a cocone on its product with a fixed left factor K, compare the
two descents from (K×X₂)⊔(K×X₃): one to the cocone apex, and one to K×X₄. Points with equal
image under the second have equal image under the first.

This is the function-level factors-through property. All spaces lie in an arbitrary universe u.
-/

/-- Let X₁→X₂, X₁→X₃, r:X₂→X₄ and b:X₃→X₄ form a pushout square in TopCat. Let K be any space and s
a cocone on the fixed-left product span K×X₁→K×X₂,K×X₁→K×X₃, with apex Z and legs s₂,s₃. If q is
the descent of id_K×r,id_K×b and g the descent of s₂,s₃, then q(z)=q(z′) implies g(z)=g(z′). -/
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
