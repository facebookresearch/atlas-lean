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
public import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Pointwise formula for fixed-left product descents

Given maps r:X₂→X₄,b:X₃→X₄ and a cocone with legs from K×X₂,K×X₃, suppose functions D_k:X₄→Z
agree with both legs on their coordinate points. The coproduct descent g is then given pointwise
by D applied to the two coordinates of the comparison descent q into K×X₄.

The formula concerns every source point; the supplied data require only a product-span cocone.
All spaces use an arbitrary universe u.
-/

/-- Let t:X₁→X₂, l:X₁→X₃, r:X₂→X₄ and b:X₃→X₄ be continuous maps, K any space, and s a cocone on the
product span id_K×t,id_K×l, with apex Z and legs s₂,s₃. Write q:(K×X₂)⊔(K×X₃)→K×X₄ for the
descent of id_K×r,id_K×b, and g for the descent of s₂,s₃. If D(k,r(x₂))=s₂(k,x₂) and
D(k,b(x₃))=s₃(k,x₃) for all coordinate points, then g(z)=D(pr₁(q(z)),pr₂(q(z))) for every z in
the coproduct. -/
theorem prodPushout_fiber_formula
    {K X₁ X₂ X₃ X₄ : TopCat.{u}}
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
            (Limits.prod.map (𝟙 K : K ⟶ K) b)) z)) := by
  have hcType :=
    isColimitOfPreserves (forget TopCat.{u})
      (coprodIsCoprod (K ⨯ X₂) (K ⨯ X₃))
  obtain ⟨⟨j⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType z
  cases j with
  | left =>
    let y₂ : ↑(K ⨯ X₂) := y
    have hy₂ : ((coprod.inl : K ⨯ X₂ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₂) = z := by
      simp only [Functor.mapCocone_ι_app, BinaryCofan.ι_app_left,
        BinaryCofan.mk_inl] at hy
      exact hy
    subst hy₂
    have hL : (coprod.desc s.inl s.inr)
        ((coprod.inl : K ⨯ X₂ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₂) =
        s.inl y₂ := by
      have h1 := CategoryTheory.ConcreteCategory.congr_hom
        (coprod.inl_desc s.inl s.inr) y₂
      rwa [CategoryTheory.ConcreteCategory.comp_apply] at h1
    have hM : (coprod.desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
        (Limits.prod.map (𝟙 K : K ⟶ K) b))
        ((coprod.inl : K ⨯ X₂ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₂) =
        (Limits.prod.map (𝟙 K : K ⟶ K) r) y₂ := by
      have h1 := CategoryTheory.ConcreteCategory.congr_hom
        (coprod.inl_desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
          (Limits.prod.map (𝟙 K : K ⟶ K) b)) y₂
      rwa [CategoryTheory.ConcreteCategory.comp_apply] at h1
    rw [hL, hM]
    have eFstMap := CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_fst (𝟙 K : K ⟶ K) r) y₂
    rw [CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.comp_apply] at eFstMap
    have hId : (𝟙 K : K ⟶ K)
        ((Limits.prod.fst : K ⨯ X₂ ⟶ K) y₂) =
        (Limits.prod.fst : K ⨯ X₂ ⟶ K) y₂ := rfl
    have hFst : (Limits.prod.fst : K ⨯ X₄ ⟶ K)
        ((Limits.prod.map (𝟙 K : K ⟶ K) r) y₂) =
        (Limits.prod.fst : K ⨯ X₂ ⟶ K) y₂ :=
      eFstMap.trans hId
    have eSndMap := CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_snd (𝟙 K : K ⟶ K) r) y₂
    rw [CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.comp_apply] at eSndMap
    have hPt : y₂ = (prodIsoProd K X₂).inv
        ((Limits.prod.fst : K ⨯ X₂ ⟶ K) y₂,
          (Limits.prod.snd : K ⨯ X₂ ⟶ X₂) y₂) := by
      apply TopCat.prod_point_ext
      · rw [TopCat.prodIsoProd_inv_fst_apply]
      · rw [TopCat.prodIsoProd_inv_snd_apply]
    have hEq := hleft ((Limits.prod.fst : K ⨯ X₂ ⟶ K) y₂)
      ((Limits.prod.snd : K ⨯ X₂ ⟶ X₂) y₂)
    rw [← hPt] at hEq
    rw [hFst, eSndMap]
    exact hEq.symm
  | right =>
    let y₃ : ↑(K ⨯ X₃) := y
    have hy₃ : ((coprod.inr : K ⨯ X₃ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₃) = z := by
      simp only [Functor.mapCocone_ι_app, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr] at hy
      exact hy
    subst hy₃
    have hL : (coprod.desc s.inl s.inr)
        ((coprod.inr : K ⨯ X₃ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₃) =
        s.inr y₃ := by
      have h1 := CategoryTheory.ConcreteCategory.congr_hom
        (coprod.inr_desc s.inl s.inr) y₃
      rwa [CategoryTheory.ConcreteCategory.comp_apply] at h1
    have hM : (coprod.desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
        (Limits.prod.map (𝟙 K : K ⟶ K) b))
        ((coprod.inr : K ⨯ X₃ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₃) =
        (Limits.prod.map (𝟙 K : K ⟶ K) b) y₃ := by
      have h1 := CategoryTheory.ConcreteCategory.congr_hom
        (coprod.inr_desc (Limits.prod.map (𝟙 K : K ⟶ K) r)
          (Limits.prod.map (𝟙 K : K ⟶ K) b)) y₃
      rwa [CategoryTheory.ConcreteCategory.comp_apply] at h1
    rw [hL, hM]
    have eFstMap := CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_fst (𝟙 K : K ⟶ K) b) y₃
    rw [CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.comp_apply] at eFstMap
    have hId : (𝟙 K : K ⟶ K)
        ((Limits.prod.fst : K ⨯ X₃ ⟶ K) y₃) =
        (Limits.prod.fst : K ⨯ X₃ ⟶ K) y₃ := rfl
    have hFst : (Limits.prod.fst : K ⨯ X₄ ⟶ K)
        ((Limits.prod.map (𝟙 K : K ⟶ K) b) y₃) =
        (Limits.prod.fst : K ⨯ X₃ ⟶ K) y₃ :=
      eFstMap.trans hId
    have eSndMap := CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_snd (𝟙 K : K ⟶ K) b) y₃
    rw [CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.comp_apply] at eSndMap
    have hPt : y₃ = (prodIsoProd K X₃).inv
        ((Limits.prod.fst : K ⨯ X₃ ⟶ K) y₃,
          (Limits.prod.snd : K ⨯ X₃ ⟶ X₃) y₃) := by
      apply TopCat.prod_point_ext
      · rw [TopCat.prodIsoProd_inv_fst_apply]
      · rw [TopCat.prodIsoProd_inv_snd_apply]
    have hEq := hright ((Limits.prod.fst : K ⨯ X₃ ⟶ K) y₃)
      ((Limits.prod.snd : K ⨯ X₃ ⟶ X₃) y₃)
    rw [← hPt] at hEq
    rw [hFst, eSndMap]
    exact hEq.symm

end TopCat
