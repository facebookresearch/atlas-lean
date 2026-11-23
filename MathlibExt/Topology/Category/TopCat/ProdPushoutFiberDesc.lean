/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Pointwise descent along a fixed-left product pushout

For one fixed `k : K`, the two product legs land at inverse-pair points.
A TopCat pushout then supplies the single-fiber descent function.
-/

/-- Single-fiber descent of a fixed-left product cocone along a pushout. -/
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
