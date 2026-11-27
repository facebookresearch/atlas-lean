/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedCellClosedEmbedding
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFactorization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorStageEq
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObjectInputs
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Smallness of realized boundaries along relative cell complexes

Let `κ` be the realized-generator cardinal. For a relative cell complex indexed
by its ordinal and built from realized boundary inclusions, morphisms from a
realized boundary domain preserve the colimit of that complex. For a complex in
an independent attachment universe, each cell-index type is required to be small
in the space universe; this ensures closed-embedding transitions.

Specializing the attachment universe to the space universe gives the cardinal
smallness instance for the realized-boundary family at `κ`.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits Topology

universe u u_1

/--
For a relative cell complex of realized boundary inclusions indexed by the
ordinal of `κ`, assume a bottom element of that ordinal and small cell-index types
in the space universe. Then `Hom(A,−)` preserves its colimit when `A` is a realized
boundary domain. The cell and space universes may be independent.
-/
theorem preservesColimit_coyoneda_of_relativeCellComplex_boundary
    [OrderBot realizedGeneratorCardinal.{u}.ord.ToType]
    {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : TopCat.realizedBoundaryInclusions i)
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u_1}
      (fun (_ : realizedGeneratorCardinal.{u}.ord.ToType) ↦
        TopCat.realizedBoundaryInclusions.homFamily) f)
    (hSmall : ∀ (j : realizedGeneratorCardinal.{u}.ord.ToType)
      (hj : ¬IsMax j), Small.{u} ((hf.attachCells j hj).ι)) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  let hClosed : TopCat.closedEmbeddings.TransfiniteCompositionOfShape
      realizedGeneratorCardinal.{u}.ord.ToType f :=
    TopCat.relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small.{u,
      u_1} TopCat.realizedBoundaryInclusions
      TopCat.realizedBoundaryInclusions_le_closedEmbeddings hf hSmall
  have hF : ∀ ⦃a b : realizedGeneratorCardinal.{u}.ord.ToType⦄
      (φ : a ⟶ b), IsClosedEmbedding ((hf.F.map φ).hom) :=
    fun _ _ φ => (TopCat.closedEmbeddings_iff _).mp (hClosed.mem_map φ)
  have : EssentiallySmall.{u} realizedGeneratorCardinal.{u}.ord.ToType :=
    EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  unfold TopCat.realizedBoundaryInclusions at hi
  rw [MorphismProperty.ofHoms_iff] at hi
  obtain ⟨n, hArrow⟩ := hi
  have hArrow' :
      Arrow.mk i = Arrow.mk (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) :=
    hArrow
  let e := eqToIso hArrow'
  have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    have hh := congrArg Arrow.Hom.left e.hom_inv_id
    rwa [Arrow.comp_left, Arrow.id_left] at hh
  refine ⟨fun {t} ht => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?hsurj ?hinj⟩
  · intro x
    obtain ⟨j, g₀, hg₀⟩ :=
      realizedBoundary_stage_exists t ht hF n (e.inv.left ≫ x)
    refine ⟨j, e.hom.left ≫ g₀, ?_⟩
    have hsurj : (e.hom.left ≫ g₀) ≫ t.ι.app j = x := by
      rw [Category.assoc, hg₀, ← Category.assoc, hleft, Category.id_comp]
    simpa using hsurj.symm
  · intro a b xa xb h
    have hTop : xa ≫ t.ι.app a = xb ≫ t.ι.app b := by simpa using h
    have h' : (e.inv.left ≫ xa) ≫ t.ι.app a =
        (e.inv.left ≫ xb) ≫ t.ι.app b := by
      rw [Category.assoc, Category.assoc, hTop]
    obtain ⟨k, p, q, huv⟩ :=
      realizedBoundary_stage_eq t ht hF n (e.inv.left ≫ xa) (e.inv.left ≫ xb) h'
    have e₁ : e.hom.left ≫ ((e.inv.left ≫ xa) ≫ hf.F.map p) =
        xa ≫ hf.F.map p := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    have e₂ : e.hom.left ≫ ((e.inv.left ≫ xb) ≫ hf.F.map q) =
        xb ≫ hf.F.map q := by
      rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
    have hpq : xa ≫ hf.F.map p = xb ≫ hf.F.map q := by
      rw [← e₁, ← e₂, huv]
    exact ⟨k, p, q, by simpa using hpq⟩

/--
The realized-boundary inclusion family satisfies the small-object cardinal
condition at `realizedGeneratorCardinal`, using colimit preservation for its
relative cell complexes.
-/
instance : MorphismProperty.IsCardinalForSmallObjectArgument
    TopCat.realizedBoundaryInclusions.{u} realizedGeneratorCardinal.{u} where
  preservesColimit i hi f hf :=
    preservesColimit_coyoneda_of_relativeCellComplex_boundary.{u, u} i hi f hf
      (fun j hj => inferInstance)
