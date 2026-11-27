/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
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
# Ordinal and sequential horn-cell descriptions

Let `I=TopCat.realizedHornInclusions.{u}` and `κ=realizedGeneratorCardinal.{u}`. The class
`I.rlp.llp` equals the retracts of `κ.ord.ToType`-indexed transfinite compositions of pushouts
of coproducts of realized horns. Retracts of `ℕ`-indexed horn-cell compositions lie in this
left class in every universe.

In universe zero, realized horn domains are separable and compact, and the countable ordinal
is also a small-object cardinal for `I`. Hence `I.rlp.llp` is exactly the retracts of
`ℕ`-indexed transfinite compositions of pushouts of coproducts of realized horn inclusions.
-/

@[expose] public section

open CategoryTheory MorphismProperty Limits Topology

universe u

namespace TopCat

/-- For every universe `u`, let `I=TopCat.realizedHornInclusions.{u}` and `κ=realizedGeneratorCardinal.{u}`. Then
`I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{u} I).pushouts κ.ord.ToType).retracts`.
The left lifting class against horn-right-lifting maps is the retract closure of this specified ordinal-shaped
relative-cell class. -/
theorem horn_rlp_llp_eq_cardinalOrd :
    realizedHornInclusions.{u}.rlp.llp =
      (transfiniteCompositionsOfShape
        (coproducts.{u} realizedHornInclusions.{u}).pushouts
        realizedGeneratorCardinal.{u}.ord.ToType).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ _

/-- For `I=TopCat.realizedHornInclusions.{u}` in any universe `u`,
`((coproducts.{u} I).pushouts.transfiniteCompositionsOfShape ℕ).retracts ≤ I.rlp.llp`.
A retract of an `ℕ`-indexed composition of pushouts of coproducts of realized horns has the left lifting property
against every map in `I.rlp`. -/
theorem horn_sequentialRetracts_le_rlp_llp :
    ((coproducts.{u} realizedHornInclusions.{u}).pushouts.transfiniteCompositionsOfShape
      ℕ).retracts ≤ realizedHornInclusions.{u}.rlp.llp :=
  retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp _ _

end TopCat

namespace TopCat

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- For `n : ℕ` and `idx : Fin (n+2)`, the realization `SSet.toTop.{0}.obj (SSet.horn.{0} (n+1)
idx)` is separable. Its realized horn inclusion is an embedding into the realization of the
standard `(n+1)`-simplex, whose usual real-simplex topology is second countable. -/
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

/-- Let `i:A→B` be a realized horn inclusion in `TopCat.{0}` and let `f:X→Y` be a relative
horn-cell complex indexed by `Cardinal.aleph0.{0}.ord.ToType`, with realized-horn attaching
family in universe zero. Then `coyoneda.obj (Opposite.op A)`, the functor `Hom(A,−)`,
preserves the colimit of the relative-cell diagram `hf.F`. -/
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

/-- The cardinal `Cardinal.aleph0.{0}` satisfies
`MorphismProperty.IsCardinalForSmallObjectArgument TopCat.realizedHornInclusions.{0}`.
Morphisms out of each realized horn domain preserve the colimits of relative horn-cell
complexes with this countable ordinal index. -/
instance : MorphismProperty.IsCardinalForSmallObjectArgument
    TopCat.realizedHornInclusions.{0} Cardinal.aleph0.{0} where
  preservesColimit i hi f hf :=
    preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0 i hi f hf

/-- For `I=TopCat.realizedHornInclusions.{0}`,
`I.rlp.llp = ((coproducts.{0} I).pushouts.transfiniteCompositionsOfShape ℕ).retracts`.
Thus, in universe zero, horn-left-lifting maps are exactly retracts of sequential compositions of pushouts of coproducts
of realized horn inclusions. -/
theorem horn_rlp_llp_eq_sequential :
    TopCat.realizedHornInclusions.{0}.rlp.llp =
      ((coproducts.{0} TopCat.realizedHornInclusions.{0}).pushouts.transfiniteCompositionsOfShape
        ℕ).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
    (I := TopCat.realizedHornInclusions.{0})

end TopCat
