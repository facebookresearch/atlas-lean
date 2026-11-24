/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedCellClosedEmbedding
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorStageEq
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFamilyFactorization
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Relative-cell smallness for realized topological generators

The coyoneda functor of a realized boundary or horn domain preserves the transfinite diagram
of a relative cell complex formed from the union of the realized boundary and horn
generators. The ordinal is the specified realized generating cardinal, and each attachment
index must be small in the stated universe. Closed transitions give stage factorization and
equality stabilization for maps from the generator domain.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits Topology

universe u u_1

/-- Morphisms out of a generator domain preserve the colimit of a
relative cell complex built from realized boundary and horn inclusions. -/
theorem preservesColimit_coyoneda_of_relativeCellComplex_generators
    [OrderBot realizedGeneratorCardinal.{u}.ord.ToType]
    {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions) i)
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u_1}
      (fun (_ : realizedGeneratorCardinal.{u}.ord.ToType) ↦
        (TopCat.realizedBoundaryInclusions ⊔
          TopCat.realizedHornInclusions).homFamily) f)
    (hSmall : ∀ (j : realizedGeneratorCardinal.{u}.ord.ToType)
      (hj : ¬IsMax j), Small.{u} ((hf.attachCells j hj).ι)) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  let hClosed : TopCat.closedEmbeddings.TransfiniteCompositionOfShape
      realizedGeneratorCardinal.{u}.ord.ToType f :=
    TopCat.relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small.{u, u_1}
      (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions)
      TopCat.realizedGenerators_le_closedEmbeddings hf hSmall
  have hF : ∀ ⦃a b : realizedGeneratorCardinal.{u}.ord.ToType⦄
      (φ : a ⟶ b), IsClosedEmbedding ((hf.F.map φ).hom) :=
    fun _ _ φ => (TopCat.closedEmbeddings_iff _).mp (hClosed.mem_map φ)
  have : EssentiallySmall.{u} realizedGeneratorCardinal.{u}.ord.ToType :=
    EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  refine ⟨fun {t} ht => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?hsurj ?hinj⟩
  · intro x
    obtain ⟨j, g', hg'⟩ := realizedGenerator_stage_exists t ht hF i hi x
    exact ⟨j, g', by simpa using hg'.symm⟩
  · intro a b xa xb h
    have h' : xa ≫ t.ι.app a = xb ≫ t.ι.app b := by simpa using h
    obtain ⟨k, p, q, hpq⟩ :=
      realizedGenerator_stage_eq t ht hF i hi xa xb h'
    exact ⟨k, p, q, by simpa using hpq⟩
