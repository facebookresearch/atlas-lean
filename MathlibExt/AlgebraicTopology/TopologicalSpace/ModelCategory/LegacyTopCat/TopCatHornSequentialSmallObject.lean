/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornRelativeCellSmallness
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Horn
public import
  MathlibExt.Topology.Category.TopCat.Embedding.TopCatHornCoproductClosedT1
public import
  MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteColimit

/-!
# Sequential small-object characterization for realized horns in `TopCat`

This file is part of the KQ3 layer, at exact base
`3ad70266a3a1a614d98acf2dedbffb7e39b943cb`.

Mathlib's small-object API fixes the transfinite shape to the witnessing
cardinal's `ord.ToType`. With the staged horn
`IsCardinalForSmallObjectArgument` instance at `realizedGeneratorCardinal`,
`realizedHornInclusions.rlp.llp` is exactly the retracts of
`realizedGeneratorCardinal.ord.ToType`-shaped transfinite compositions of
pushouts of coproducts of realized horns
(`horn_rlp_llp_eq_cardinalOrd`). That shaped equality is the exact-shape
output of the current pin; the unshaped `transfiniteCompositions` equality
already used by the conditional horn-cell assembly is not restated here.

At universe zero, realized horns are additionally `aleph0`-small for the
small-object argument: horn domains are compact separable, so coyoneda
preserves the colimit of every `Cardinal.aleph0.ord.ToType`-shaped horn
relative-cell diagram
(`preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0`). Hence
`realizedHornInclusions.{0}.rlp.llp` is exactly the retracts of
`ℕ`-shaped transfinite compositions of pushouts of coproducts of realized
horns (`horn_rlp_llp_eq_sequential`), via
`SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0`. The
reverse inclusion (`horn_sequentialRetracts_le_rlp_llp`) is retained as the
universe-general half.

No weak-equivalence, factorization-system, or model-category claim is made
here, and no KQ4 content is used.
-/

@[expose] public section

open CategoryTheory MorphismProperty Limits Topology

universe u

namespace TopCat

/-- Exact pinned shape: the horn left class is retracts of
`realizedGeneratorCardinal.ord.ToType`-shaped cell compositions. -/
theorem horn_rlp_llp_eq_cardinalOrd :
    realizedHornInclusions.{u}.rlp.llp =
      (transfiniteCompositionsOfShape
        (coproducts.{u} realizedHornInclusions.{u}).pushouts
        realizedGeneratorCardinal.{u}.ord.ToType).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ _

/-- Sequential half available now: retracts of `ℕ`-shaped horn-cell
compositions lie in the horn left class. -/
theorem horn_sequentialRetracts_le_rlp_llp :
    ((coproducts.{u} realizedHornInclusions.{u}).pushouts.transfiniteCompositionsOfShape
      ℕ).retracts ≤ realizedHornInclusions.{u}.rlp.llp :=
  retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp _ _

end TopCat

namespace TopCat

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- Horn domains are separable: the realized standard simplex is
second-countable across `SimplexCategory.toTopHomeo`, and the realized horn
inclusion is an embedding. -/
private theorem separableSpace_hornDomain (n : ℕ) (idx : Fin (n + 2)) :
    TopologicalSpace.SeparableSpace
      ↥(SSet.toTop.{0}.obj (SSet.horn.{0} (n + 1) idx)) := by
  have hStd : SecondCountableTopology
      (Convexity.StdSimplex ℝ (Fin ((SimplexCategory.mk (n + 1)).len + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).secondCountableTopology
  have hSC : SecondCountableTopology
      ↥(SSet.toTop.{0}.obj (SSet.stdSimplex.{0}.obj (SimplexCategory.mk (n + 1)))) :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).secondCountableTopology
  have hEmb : IsEmbedding
      ⇑(SSet.toTop.{0}.map (SSet.horn.{0} (n + 1) idx).ι).hom :=
    ((TopCat.closedEmbeddings_iff _).mp
      (SSet.horn.closedEmbeddings_toTop_map_ι (n + 1) idx)).isEmbedding
  exact @Topology.IsEmbedding.separableSpace _ _ _ _ hSC _ hEmb

/-- Morphisms out of a horn domain preserve the colimit of an
`aleph0`-shaped relative cell complex built from realized horn inclusions:
surjectivity is compact-separable stage factorization, and injectivity
cancels a closed-embedding colimit leg at the same stage. -/
theorem preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0
    {A B : TopCat.{0}} (i : A ⟶ B)
    (hi : TopCat.realizedHornInclusions.{0} i)
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : HomotopicalAlgebra.RelativeCellComplex.{0}
      (fun (_ : Cardinal.aleph0.{0}.ord.ToType) ↦
        TopCat.realizedHornInclusions.{0}.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  unfold TopCat.realizedHornInclusions at hi
  rw [MorphismProperty.iSup_iff] at hi
  obtain ⟨n, hn⟩ := hi
  rw [MorphismProperty.ofHoms_iff] at hn
  obtain ⟨idx, hArrow⟩ := hn
  have hArrow' :
      Arrow.mk i =
        Arrow.mk (SSet.toTop.{0}.map (SSet.horn.{0} (n + 1) idx).ι) :=
    hArrow
  let e := eqToIso hArrow'
  have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    have hh := congrArg Arrow.Hom.left e.hom_inv_id
    rwa [Arrow.comp_left, Arrow.id_left] at hh
  have hF : ∀ ⦃a b : Cardinal.aleph0.{0}.ord.ToType⦄ (φ : a ⟶ b),
      TopCat.closedT1Embeddings (hf.F.map φ) := by
    intro a b φ
    simpa only [HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape,
      MorphismProperty.TransfiniteCompositionOfShape.ofLE] using
      ((HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape _ hf).ofLE
        (by simpa only [MorphismProperty.ofHoms_homFamily] using
          TopCat.pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings)).mem_map φ
  have hFclosed : ∀ ⦃a b : Cardinal.aleph0.{0}.ord.ToType⦄ (φ : a ⟶ b),
      IsClosedEmbedding (hf.F.map φ).hom :=
    fun _ _ φ => TopCat.closedT1Embeddings_le_isClosedEmbedding _ (hF φ)
  have hSep : TopologicalSpace.SeparableSpace
      ↥(SSet.toTop.{0}.obj (SSet.horn.{0} (n + 1) idx)) :=
    separableSpace_hornDomain n idx
  have hComp : IsCompact (Set.univ : Set
      ↥(SSet.toTop.{0}.obj (SSet.horn.{0} (n + 1) idx))) :=
    isCompact_univ
  refine ⟨fun {t} ht => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?hsurj ?hinj⟩
  · intro x
    obtain ⟨j, g₀, hg₀⟩ :=
      @TopCat.exists_stage_of_compact_transfinite _ _ _ _ t ht hF _ _ hSep
        hComp (e.inv.left ≫ x).hom
    have hg₀' : TopCat.ofHom g₀ ≫ t.ι.app j = e.inv.left ≫ x := by
      apply TopCat.hom_ext
      simpa using hg₀
    refine ⟨j, e.hom.left ≫ TopCat.ofHom g₀, ?_⟩
    have hcomp : (e.hom.left ≫ TopCat.ofHom g₀) ≫ t.ι.app j = x := by
      rw [Category.assoc, hg₀', ← Category.assoc, hleft, Category.id_comp]
    simpa using hcomp.symm
  · intro j x y h
    have hTop : x ≫ t.ι.app j = y ≫ t.ι.app j := by simpa using h
    have hLeg : IsClosedEmbedding (t.ι.app j).hom :=
      TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding t ht hFclosed j
    have hEq : x = y := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      apply hLeg.injective
      simpa using ConcreteCategory.congr_hom hTop a
    exact ⟨j, 𝟙 j, by simpa using hEq⟩

/-- Small-object cardinal instance for realized horns at `aleph0`. -/
instance : MorphismProperty.IsCardinalForSmallObjectArgument
    TopCat.realizedHornInclusions.{0} Cardinal.aleph0.{0} where
  preservesColimit i hi f hf :=
    preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0 i hi f hf

/-- Sequential equality at universe zero: the horn left class is retracts of
`ℕ`-shaped horn-cell compositions. -/
theorem horn_rlp_llp_eq_sequential :
    TopCat.realizedHornInclusions.{0}.rlp.llp =
      ((coproducts.{0} TopCat.realizedHornInclusions.{0}).pushouts.transfiniteCompositionsOfShape
        ℕ).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
    (I := TopCat.realizedHornInclusions.{0})

end TopCat
