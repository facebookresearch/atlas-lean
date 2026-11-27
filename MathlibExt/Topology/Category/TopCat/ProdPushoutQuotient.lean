/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import MathlibExt.Topology.Convenient.QuotientProduct
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat Topology

universe u

namespace TopCat

/-!
# Quotient maps for fixed-left product descents

For any spaces K,X,Y, the chosen coproduct (K×X)⊔(K×Y) is homeomorphic to K×(X⊕Y), preserving
the left product coordinate and the two sum branches.

Under this chart, a quotient map id_K×[r,b] induces a quotient coproduct descent to K×X₄. If X₄
is a pushout and K locally compact, that descent is a quotient map. All spaces are in an
arbitrary universe u.
-/

/-- For spaces K,X,Y, the canonical homeomorphism (K×X)⊔(K×Y)≅K×(X⊕Y) preserves K as the left factor
and labels the two coproduct branches by the sum injections. -/
noncomputable def prodCoproductEmbed (K X Y : TopCat.{u}) :
    (↑((K ⨯ X) ⨿ (K ⨯ Y)) : Type u) ≃ₜ (↑K × (↑X ⊕ ↑Y)) :=
  ((coprodHomeomorphSum _ _).trans
    (Homeomorph.sumCongr (homeoOfIso (prodIsoProd K X))
      (homeoOfIso (prodIsoProd K Y)))).trans
    Homeomorph.prodSumDistrib.symm

private theorem midMap_inl {K X₂ X₃ X₄ : TopCat.{u}} (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)
    (k : ↑K) (x : ↑X₂) :
    Prod.map id (Sum.elim r b) (k, Sum.inl x) = (k, r x) := rfl

private theorem midMap_inr {K X₂ X₃ X₄ : TopCat.{u}} (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)
    (k : ↑K) (x : ↑X₃) :
    Prod.map id (Sum.elim r b) (k, Sum.inr x) = (k, b x) := rfl

/-- For the product-coproduct homeomorphism, the left point inl(k,x) maps to (k,Sum.inl x), using
the canonical product charts. -/
@[simp]
theorem prodCoproductEmbed_inl (K X Y : TopCat.{u}) (a : ↑(K ⨯ X)) :
    prodCoproductEmbed K X Y ((coprod.inl : K ⨯ X ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) a) =
      ((Limits.prod.fst : K ⨯ X ⟶ K) a, Sum.inl ((Limits.prod.snd : K ⨯ X ⟶ X) a)) := by
  apply Homeomorph.prodSumDistrib.injective
  have hA : Homeomorph.prodSumDistrib (prodCoproductEmbed K X Y
      ((coprod.inl : K ⨯ X ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) a)) =
      (Homeomorph.sumCongr (homeoOfIso (prodIsoProd K X))
        (homeoOfIso (prodIsoProd K Y))) (coprodHomeomorphSum _ _
        ((coprod.inl : K ⨯ X ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) a)) :=
    Homeomorph.apply_symm_apply _ _
  rw [hA, coprodHomeomorphSum_inl]
  change Sum.inl ((prodIsoProd K X).hom a) = Homeomorph.prodSumDistrib
    ((Limits.prod.fst : K ⨯ X ⟶ K) a, Sum.inl ((Limits.prod.snd : K ⨯ X ⟶ X) a))
  rw [prodIsoProd_hom_apply]
  rfl

/-- For the product-coproduct homeomorphism, the right point inr(k,y) maps to (k,Sum.inr y), using
the canonical product charts. -/
@[simp]
theorem prodCoproductEmbed_inr (K X Y : TopCat.{u}) (b : ↑(K ⨯ Y)) :
    prodCoproductEmbed K X Y ((coprod.inr : K ⨯ Y ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) b) =
      ((Limits.prod.fst : K ⨯ Y ⟶ K) b, Sum.inr ((Limits.prod.snd : K ⨯ Y ⟶ Y) b)) := by
  apply Homeomorph.prodSumDistrib.injective
  have hA : Homeomorph.prodSumDistrib (prodCoproductEmbed K X Y
      ((coprod.inr : K ⨯ Y ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) b)) =
      (Homeomorph.sumCongr (homeoOfIso (prodIsoProd K X))
        (homeoOfIso (prodIsoProd K Y))) (coprodHomeomorphSum _ _
        ((coprod.inr : K ⨯ Y ⟶ (K ⨯ X) ⨿ (K ⨯ Y)) b)) :=
    Homeomorph.apply_symm_apply _ _
  rw [hA, coprodHomeomorphSum_inr]
  change Sum.inr ((prodIsoProd K Y).hom b) = Homeomorph.prodSumDistrib
    ((Limits.prod.fst : K ⨯ Y ⟶ K) b, Sum.inr ((Limits.prod.snd : K ⨯ Y ⟶ Y) b))
  rw [prodIsoProd_hom_apply]
  rfl

/-- For continuous r:X₂→X₄,b:X₃→X₄, suppose id_K×[r,b]:K×(X₂⊕X₃)→K×X₄ is a quotient map. Then the
descent (K×X₂)⊔(K×X₃)→K×X₄ of id_K×r,id_K×b is a quotient map. -/
theorem isQuotientMap_coprodDesc_prodMap_of_quotientProd
    {K X₂ X₃ X₄ : TopCat.{u}}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (hqm : IsQuotientMap (Prod.map id (Sum.elim r b) :
      ↑K × (↑X₂ ⊕ ↑X₃) → ↑K × ↑X₄)) :
    IsQuotientMap (coprod.desc (Limits.prod.map (𝟙 K) r)
      (Limits.prod.map (𝟙 K) b)) := by
  have hEq : ⇑(coprod.desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b)) =
      ⇑(homeoOfIso (prodIsoProd K X₄)).symm ∘
        (Prod.map id (Sum.elim r b) ∘ ⇑(prodCoproductEmbed K X₂ X₃)) := by
    funext p
    simp only [Function.comp_apply]
    have hcType := isColimitOfPreserves (forget TopCat.{u}) (coprodIsCoprod (K ⨯ X₂) (K ⨯ X₃))
    obtain ⟨⟨j⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType p
    cases j with
    | left =>
      let y₂ : ↑(K ⨯ X₂) := y
      have hy₂ : ((coprod.inl : K ⨯ X₂ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₂) = p := by
        simp only [Functor.mapCocone_ι_app, BinaryCofan.ι_app_left,
          BinaryCofan.mk_inl] at hy
        exact hy
      subst hy₂
      have hL : (coprod.desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b))
          ((coprod.inl : K ⨯ X₂ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₂) =
          (Limits.prod.map (𝟙 K) r) y₂ := by
        have h1 := ConcreteCategory.congr_hom
          (coprod.inl_desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b)) y₂
        rwa [ConcreteCategory.comp_apply] at h1
      rw [prodCoproductEmbed_inl, midMap_inl, hL]
      apply (homeoOfIso (prodIsoProd K X₄)).injective
      rw [Homeomorph.apply_symm_apply]
      change ((prodIsoProd K X₄).hom) ((Limits.prod.map (𝟙 K) r) y₂) = _
      rw [prodIsoProd_hom_apply]
      congr 1
      · have hfst := ConcreteCategory.congr_hom (Limits.prod.map_fst (𝟙 K) r) y₂
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hfst
        exact hfst
      · have hsnd := ConcreteCategory.congr_hom (Limits.prod.map_snd (𝟙 K) r) y₂
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hsnd
        exact hsnd
    | right =>
      let y₃ : ↑(K ⨯ X₃) := y
      have hy₃ : ((coprod.inr : K ⨯ X₃ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₃) = p := by
        simp only [Functor.mapCocone_ι_app, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr] at hy
        exact hy
      subst hy₃
      have hL : (coprod.desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b))
          ((coprod.inr : K ⨯ X₃ ⟶ (K ⨯ X₂) ⨿ (K ⨯ X₃)) y₃) =
          (Limits.prod.map (𝟙 K) b) y₃ := by
        have h1 := ConcreteCategory.congr_hom
          (coprod.inr_desc (Limits.prod.map (𝟙 K) r) (Limits.prod.map (𝟙 K) b)) y₃
        rwa [ConcreteCategory.comp_apply] at h1
      rw [prodCoproductEmbed_inr, midMap_inr, hL]
      apply (homeoOfIso (prodIsoProd K X₄)).injective
      rw [Homeomorph.apply_symm_apply]
      change ((prodIsoProd K X₄).hom) ((Limits.prod.map (𝟙 K) b) y₃) = _
      rw [prodIsoProd_hom_apply]
      congr 1
      · have hfst := ConcreteCategory.congr_hom (Limits.prod.map_fst (𝟙 K) b) y₃
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hfst
        exact hfst
      · have hsnd := ConcreteCategory.congr_hom (Limits.prod.map_snd (𝟙 K) b) y₃
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hsnd
        exact hsnd
  have hQ : IsQuotientMap (⇑(homeoOfIso (prodIsoProd K X₄)).symm ∘
      (Prod.map id (Sum.elim r b) ∘ ⇑(prodCoproductEmbed K X₂ X₃))) :=
    IsQuotientMap.comp (homeoOfIso (prodIsoProd K X₄)).symm.isQuotientMap
      (IsQuotientMap.comp hqm (prodCoproductEmbed K X₂ X₃).isQuotientMap)
  rwa [hEq]

/-- Let X₁→X₂, X₁→X₃, r:X₂→X₄ and b:X₃→X₄ form a pushout square in TopCat. If K is locally compact,
the canonical descent (K×X₂)⊔(K×X₃)→K×X₄ is a quotient map. -/
theorem isQuotientMap_coprodDesc_prodMap_of_isPushout
    {K X₁ X₂ X₃ X₄ : TopCat.{u}} [LocallyCompactSpace ↑K]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) :
    IsQuotientMap (coprod.desc (Limits.prod.map (𝟙 K) r)
      (Limits.prod.map (𝟙 K) b)) := by
  have hq : IsQuotientMap (Sum.elim r b : ↑X₂ ⊕ ↑X₃ → ↑X₄) :=
    isQuotientMap_sumElim_of_isPushout h
  have hqm : IsQuotientMap (Prod.map id (Sum.elim r b) :
      ↑K × (↑X₂ ⊕ ↑X₃) → ↑K × ↑X₄) := hq.prodMap_right
  exact isQuotientMap_coprodDesc_prodMap_of_quotientProd hqm

end TopCat
