/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Function descent in one product fiber

Let X₄ be a pushout of X₂ and X₃ over X₁, and let s be a cocone after multiplying the span on
the left by K. For each fixed k∈K, there is a function d_k:X₄→s.pt agreeing with the two cocone
legs at the coordinate points (k,x).

The formulas use the canonical product charts. The conclusion supplies a function in each fiber,
in an arbitrary universe u.
-/

/-- Let X₁→X₂, X₁→X₃, r:X₂→X₄ and b:X₃→X₄ form a pushout square in TopCat. Let K be any space and s
a cocone on the fixed-left product span K×X₁→K×X₂,K×X₁→K×X₃, with apex Z and legs s₂,s₃. For
each k∈K, there is a function d_k:X₄→Z with d_k(r(x₂))=s₂(k,x₂) and d_k(b(x₃))=s₃(k,x₃), under
the canonical product-coordinate charts. -/
theorem exists_prodMap_fiber_desc_of_isPushout
    {K X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b)
    (s : PushoutCocone (Limits.prod.map (𝟙 K) t) (Limits.prod.map (𝟙 K) l))
    (k : ↑K) :
    ∃ (d : ↑X₄ → ↑s.pt),
      (∀ x : ↑X₂, d (r x) = s.inl ((prodIsoProd K X₂).inv (k, x))) ∧
      (∀ x : ↑X₃, d (b x) = s.inr ((prodIsoProd K X₃).inv (k, x))) := by
  let hT := h.map (forget TopCat)
  let f₂ : ((forget TopCat).obj X₂ ⟶ (forget TopCat).obj s.pt) :=
    TypeCat.ofHom fun x => s.inl ((prodIsoProd K X₂).inv (k, x))
  let f₃ : ((forget TopCat).obj X₃ ⟶ (forget TopCat).obj s.pt) :=
    TypeCat.ofHom fun x => s.inr ((prodIsoProd K X₃).inv (k, x))
  have compat : (forget TopCat).map t ≫ f₂ = (forget TopCat).map l ≫ f₃ := by
    ext x₁
    have hcond := CategoryTheory.ConcreteCategory.congr_hom s.condition
      ((prodIsoProd K X₁).inv (k, x₁))
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hcond
    rw [TopCat.prodMap_prodIso_inv_apply, TopCat.prodMap_prodIso_inv_apply] at hcond
    exact hcond
  obtain ⟨d, hd₂, hd₃⟩ := hT.exists_desc f₂ f₃ compat
  refine ⟨d, ?_, ?_⟩
  · intro x₂
    have h₂ := CategoryTheory.ConcreteCategory.congr_hom hd₂ x₂
    exact h₂
  · intro x₃
    have h₃ := CategoryTheory.ConcreteCategory.congr_hom hd₃ x₃
    exact h₃

end TopCat
