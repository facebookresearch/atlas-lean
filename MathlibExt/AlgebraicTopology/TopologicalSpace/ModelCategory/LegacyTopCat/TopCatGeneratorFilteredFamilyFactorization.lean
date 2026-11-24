/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFactorization

/-!
# Uniform stage factorization for realized generator families

For a morphism in
`TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`, every
`TopCat` map from its domain into the colimit of a filtered diagram with
closed-embedding transitions factors through some stage.

The proof splits only the generator-family membership, recovers the
corresponding boundary or horn arrow up to the `Arrow` isomorphism from
`ofHoms`/`iSup` membership, transports the domain map, applies
`realizedBoundary_stage_exists` or `realizedHorn_stage_exists`, and transports
back.

Not a `TopCat` presentability, small-object, factorization-system, cofibration,
weak-equivalence, or model-structure claim.
-/

@[expose] public section

open CategoryTheory Limits Topology

universe u v w

theorem realizedGenerator_stage_exists
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions) f)
    (g : A ⟶ c.pt) :
    ∃ (j : J) (g' : A ⟶ F.obj j), g' ≫ c.ι.app j = g := by
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
      have h := congrArg Arrow.Hom.left e.hom_inv_id
      rwa [Arrow.comp_left, Arrow.id_left] at h
    obtain ⟨j, g₀, hg₀⟩ :=
      realizedBoundary_stage_exists c hc hF n (e.inv.left ≫ g)
    refine ⟨j, e.hom.left ≫ g₀, ?_⟩
    rw [Category.assoc, hg₀, ← Category.assoc, hleft]
    exact Category.id_comp g
  | inr hfH =>
    unfold TopCat.realizedHornInclusions at hfH
    rw [MorphismProperty.iSup_iff] at hfH
    obtain ⟨n, hn⟩ := hfH
    rw [MorphismProperty.ofHoms_iff] at hn
    obtain ⟨i, hArrow⟩ := hn
    have hArrow' :
        Arrow.mk f =
          Arrow.mk (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι) :=
      hArrow
    let e := eqToIso hArrow'
    have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
      have h := congrArg Arrow.Hom.left e.hom_inv_id
      rwa [Arrow.comp_left, Arrow.id_left] at h
    obtain ⟨j, g₀, hg₀⟩ :=
      realizedHorn_stage_exists c hc hF (n + 1) i (e.inv.left ≫ g)
    refine ⟨j, e.hom.left ≫ g₀, ?_⟩
    rw [Category.assoc, hg₀, ← Category.assoc, hleft]
    exact Category.id_comp g
