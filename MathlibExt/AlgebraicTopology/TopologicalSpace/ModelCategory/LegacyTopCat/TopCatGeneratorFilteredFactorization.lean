/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorPresentability
public import MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit

/-!
# Factorization from realized generators through closed filtered colimits

Let `κ` be the realized-generator cardinal, assumed regular. For an essentially
small `κ`-filtered diagram of topological spaces with closed-embedding transitions,
every map from a realized simplicial boundary or horn to its colimit factors
through some stage.

The space universe and the object and morphism universes of the index category
are independent. The underlying-type presentability gives the stage function,
and the closed-embedding colimit inclusion ensures its continuity.
-/

@[expose] public section

open CategoryTheory Limits Topology

universe u v w

/--
For an essentially small `κ`-filtered diagram with closed-embedding transitions
and regular `κ`, a continuous map from a realized boundary to the colimit factors
as a continuous map to some stage followed by that stage's colimit inclusion.
-/
theorem realizedBoundary_stage_exists
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) (f : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ c.pt) :
    ∃ (j : J) (g : SSet.toTop.{u}.obj (SSet.boundary.{u} n) ⟶ F.obj j),
      g ≫ c.ι.app j = f := by
  have hPresent : IsCardinalPresentable ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} :=
    isCardinalPresentable_realizedBoundary.{u} n
  have hFilt : IsFiltered J :=
    isFiltered_of_isCardinalFiltered J realizedGeneratorCardinal.{u}
  obtain ⟨j, f', hf'⟩ :=
    @IsCardinalPresentable.exists_hom_of_isColimit
      (X := ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n)))
      (κ := realizedGeneratorCardinal.{u}) (Type u) inferInstance inferInstance J
      inferInstance hPresent inferInstance inferInstance _ _
      (isColimitOfPreserves (forget TopCat) hc) ((forget TopCat).map f)
  let stageTop : TopologicalSpace ((F ⋙ forget TopCat).obj j) := (F.obj j).str
  have hClosed : IsClosedEmbedding (c.ι.app j).hom :=
    @TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding J inferInstance hFilt
      F c hc hF j
  have hEmb : IsEmbedding (c.ι.app j).hom := hClosed.isEmbedding
  have h_eq :
      ⇑(c.ι.app j).hom ∘
          (f' : ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n)) → ↥(F.obj j)) =
        ⇑f.hom := by
    apply funext
    intro x
    exact ConcreteCategory.congr_hom hf' x
  have hcomp :
      Continuous
        (⇑(c.ι.app j).hom ∘
          (f' : ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n)) → ↥(F.obj j))) := by
    rw [h_eq]
    exact f.hom.continuous_toFun
  have hcont :
      @Continuous _ _ _ stageTop
        (f' : ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n)) → ↥(F.obj j)) :=
    hEmb.continuous_iff.mpr hcomp
  refine ⟨j, TopCat.ofHom ⟨f', hcont⟩, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrFun h_eq x

/--
For an essentially small `κ`-filtered diagram with closed-embedding transitions
and regular `κ`, a continuous map from a realized horn to the colimit factors
through a continuous map to some stage.
-/
theorem realizedHorn_stage_exists
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
    [Fact realizedGeneratorCardinal.{u}.IsRegular]
    [IsCardinalFiltered J realizedGeneratorCardinal.{u}]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (n : ℕ) (i : Fin (n + 1))
    (f : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ c.pt) :
    ∃ (j : J) (g : SSet.toTop.{u}.obj (SSet.horn.{u} n i) ⟶ F.obj j),
      g ≫ c.ι.app j = f := by
  have hPresent : IsCardinalPresentable ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} :=
    isCardinalPresentable_realizedHorn.{u} n i
  have hFilt : IsFiltered J :=
    isFiltered_of_isCardinalFiltered J realizedGeneratorCardinal.{u}
  obtain ⟨j, f', hf'⟩ :=
    @IsCardinalPresentable.exists_hom_of_isColimit
      (X := ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i)))
      (κ := realizedGeneratorCardinal.{u}) (Type u) inferInstance inferInstance J
      inferInstance hPresent inferInstance inferInstance _ _
      (isColimitOfPreserves (forget TopCat) hc) ((forget TopCat).map f)
  let stageTop : TopologicalSpace ((F ⋙ forget TopCat).obj j) := (F.obj j).str
  have hClosed : IsClosedEmbedding (c.ι.app j).hom :=
    @TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding J inferInstance hFilt
      F c hc hF j
  have hEmb : IsEmbedding (c.ι.app j).hom := hClosed.isEmbedding
  have h_eq :
      ⇑(c.ι.app j).hom ∘
          (f' : ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i)) → ↥(F.obj j)) =
        ⇑f.hom := by
    apply funext
    intro x
    exact ConcreteCategory.congr_hom hf' x
  have hcomp :
      Continuous
        (⇑(c.ι.app j).hom ∘
          (f' : ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i)) → ↥(F.obj j))) := by
    rw [h_eq]
    exact f.hom.continuous_toFun
  have hcont :
      @Continuous _ _ _ stageTop
        (f' : ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i)) → ↥(F.obj j)) :=
    hEmb.continuous_iff.mpr hcomp
  refine ⟨j, TopCat.ofHom ⟨f', hcont⟩, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrFun h_eq x
