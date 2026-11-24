/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorPresentability

/-!
# Stage equality for realized generator factorizations

Two factorizations of a boundary or horn map through stages of a filtered
diagram with closed-embedding transitions that agree in the colimit agree
after passage to a common later stage, with a uniform transport for
`TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`
mirroring `realizedGenerator_stage_exists`.

Function-level equality is `IsCardinalPresentable.exists_eq_of_isColimit` at
`realizedGeneratorCardinal`; `TopCat` equality follows by `TopCat.hom_ext`.

Not a `TopCat` presentability, small-object, factorization-system, cofibration,
weak-equivalence, or model-structure claim.
-/

@[expose] public section

open CategoryTheory Limits Topology

universe u v w

theorem realizedBoundary_stage_eq
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (_hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) {j₁ j₂ : J}
    (g₁ : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j₁)
    (g₂ : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v := by
  have hPresent : IsCardinalPresentable ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} :=
    isCardinalPresentable_realizedBoundary.{u} n
  have hfType : (forget TopCat.{u}).map g₁ ≫ (forget TopCat.{u}).map (c.ι.app j₁) =
      (forget TopCat.{u}).map g₂ ≫ (forget TopCat.{u}).map (c.ι.app j₂) := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  obtain ⟨k, u, v, huv⟩ :=
    IsCardinalPresentable.exists_eq_of_isColimit realizedGeneratorCardinal.{u}
      (isColimitOfPreserves (forget TopCat.{u}) hc)
      ((forget TopCat.{u}).map g₁) ((forget TopCat.{u}).map g₂) hfType
  refine ⟨k, u, v, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact ConcreteCategory.congr_hom huv x

theorem realizedHorn_stage_eq
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (_hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) (i : Fin (n + 1)) {j₁ j₂ : J}
    (g₁ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₁)
    (g₂ : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v := by
  have hPresent : IsCardinalPresentable ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} :=
    isCardinalPresentable_realizedHorn.{u} n i
  have hfType : (forget TopCat.{u}).map g₁ ≫ (forget TopCat.{u}).map (c.ι.app j₁) =
      (forget TopCat.{u}).map g₂ ≫ (forget TopCat.{u}).map (c.ι.app j₂) := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  obtain ⟨k, u, v, huv⟩ :=
    IsCardinalPresentable.exists_eq_of_isColimit realizedGeneratorCardinal.{u}
      (isColimitOfPreserves (forget TopCat.{u}) hc)
      ((forget TopCat.{u}).map g₁) ((forget TopCat.{u}).map g₂) hfType
  refine ⟨k, u, v, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact ConcreteCategory.congr_hom huv x

theorem realizedGenerator_stage_eq
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions) f)
    {j₁ j₂ : J} (g₁ : A ⟶ F.obj j₁) (g₂ : A ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (u : j₁ ⟶ k) (v : j₂ ⟶ k),
      g₁ ≫ F.map u = g₂ ≫ F.map v := by
  rw [MorphismProperty.sup_iff] at hf
  cases hf with
  | inl hfB =>
    unfold TopCat.realizedBoundaryInclusions at hfB
    rw [MorphismProperty.ofHoms_iff] at hfB
    obtain ⟨n, hArrow⟩ := hfB
    have hArrow' :
        Arrow.mk f = Arrow.mk (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) :=
      hArrow
    let e := eqToIso hArrow'
    have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
      have hh := congrArg Arrow.Hom.left e.hom_inv_id
      rwa [Arrow.comp_left, Arrow.id_left] at hh
    have h' : (e.inv.left ≫ g₁) ≫ c.ι.app j₁ =
        (e.inv.left ≫ g₂) ≫ c.ι.app j₂ := by
      rw [Category.assoc, Category.assoc, h]
    obtain ⟨k, u, v, huv⟩ :=
      realizedBoundary_stage_eq c hc hF n (e.inv.left ≫ g₁) (e.inv.left ≫ g₂) h'
    refine ⟨k, u, v, ?_⟩
    have e₁ : e.hom.left ≫ ((e.inv.left ≫ g₁) ≫ F.map u) = g₁ ≫ F.map u := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    have e₂ : e.hom.left ≫ ((e.inv.left ≫ g₂) ≫ F.map v) = g₂ ≫ F.map v := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    rw [← e₁, ← e₂, huv]
  | inr hfH =>
    unfold TopCat.realizedHornInclusions at hfH
    rw [MorphismProperty.iSup_iff] at hfH
    obtain ⟨n, hn⟩ := hfH
    rw [MorphismProperty.ofHoms_iff] at hn
    obtain ⟨i, hArrow⟩ := hn
    have hArrow' :
        Arrow.mk f = Arrow.mk (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι) :=
      hArrow
    let e := eqToIso hArrow'
    have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
      have hh := congrArg Arrow.Hom.left e.hom_inv_id
      rwa [Arrow.comp_left, Arrow.id_left] at hh
    have h' : (e.inv.left ≫ g₁) ≫ c.ι.app j₁ =
        (e.inv.left ≫ g₂) ≫ c.ι.app j₂ := by
      rw [Category.assoc, Category.assoc, h]
    obtain ⟨k, u, v, huv⟩ := realizedHorn_stage_eq c hc hF (n + 1) i
      (e.inv.left ≫ g₁) (e.inv.left ≫ g₂) h'
    refine ⟨k, u, v, ?_⟩
    have e₁ : e.hom.left ≫ ((e.inv.left ≫ g₁) ≫ F.map u) = g₁ ≫ F.map u := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    have e₂ : e.hom.left ≫ ((e.inv.left ≫ g₂) ≫ F.map v) = g₂ ≫ F.map v := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    rw [← e₁, ← e₂, huv]
