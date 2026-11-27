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
# Smallness of realized horn domains along relative cell complexes

Let `I` be the class of realized horn inclusions in `TopCat.{u}` and let
`κ=realizedGeneratorCardinal.{u}`. If `i:A→B` belongs to `I` and `f:X→Y` is a
`κ.ord.ToType`-indexed relative `I`-cell complex, with each attaching-cell index small in
universe `u`, then the functor `Hom(A,−)` preserves the colimit of its transfinite diagram.
The ordinal index is assumed to have a least element.

These colimit-preservation statements give `IsCardinalForSmallObjectArgument I κ`: the chosen
generator cardinal is a small-object cardinal for realized horns.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits Topology

universe u u_1

/-- Let `κ=realizedGeneratorCardinal.{u}` and equip `κ.ord.ToType` with an `OrderBot`. Let `i:A→B`
be a realized horn inclusion in `TopCat.{u}` and `f:X→Y` a relative cell complex indexed by
`κ.ord.ToType`, with realized-horn attaching family at each stage. Assume every nonmaximal
stage's attaching index `(hf.attachCells j hj).ι` is `Small.{u}`. Then `coyoneda.obj
(Opposite.op A)`, the functor `Hom(A,−)`, preserves the colimit of `hf.F`. -/
theorem preservesColimit_coyoneda_of_relativeCellComplex_horn
    [OrderBot realizedGeneratorCardinal.{u}.ord.ToType]
    {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : TopCat.realizedHornInclusions i)
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u_1}
      (fun (_ : realizedGeneratorCardinal.{u}.ord.ToType) ↦
        TopCat.realizedHornInclusions.homFamily) f)
    (hSmall : ∀ (j : realizedGeneratorCardinal.{u}.ord.ToType)
      (hj : ¬IsMax j), Small.{u} ((hf.attachCells j hj).ι)) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  unfold TopCat.realizedHornInclusions at hi
  rw [MorphismProperty.iSup_iff] at hi
  obtain ⟨n, hn⟩ := hi
  rw [MorphismProperty.ofHoms_iff] at hn
  obtain ⟨idx, hArrow⟩ := hn
  have hArrow' :
      Arrow.mk i =
        Arrow.mk (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) idx).ι) :=
    hArrow
  let e := eqToIso hArrow'
  have hleft : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    have hh := congrArg Arrow.Hom.left e.hom_inv_id
    rwa [Arrow.comp_left, Arrow.id_left] at hh
  let hClosed : TopCat.closedEmbeddings.TransfiniteCompositionOfShape
      realizedGeneratorCardinal.{u}.ord.ToType f :=
    TopCat.relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small.{u, u_1}
      (I := TopCat.realizedHornInclusions)
      (hI := TopCat.realizedHornInclusions_le_closedEmbeddings) (c := hf)
      (hSmall := hSmall)
  have hF : ∀ ⦃a b : realizedGeneratorCardinal.{u}.ord.ToType⦄
      (φ : a ⟶ b), IsClosedEmbedding ((hf.F.map φ).hom) :=
    fun _ _ φ => (TopCat.closedEmbeddings_iff _).mp (hClosed.mem_map φ)
  have : EssentiallySmall.{u} realizedGeneratorCardinal.{u}.ord.ToType :=
    EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  refine ⟨fun {t} ht => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?hsurj ?hinj⟩
  · intro x
    obtain ⟨j, g₀, hg₀⟩ := realizedHorn_stage_exists t ht hF (n + 1) idx
      (e.inv.left ≫ x)
    refine ⟨j, e.hom.left ≫ g₀, ?_⟩
    have hcomp : (e.hom.left ≫ g₀) ≫ t.ι.app j = x := by
      rw [Category.assoc, hg₀, ← Category.assoc, hleft, Category.id_comp]
    simpa using hcomp.symm
  · intro a b xa xb h
    have hTop : xa ≫ t.ι.app a = xb ≫ t.ι.app b := by simpa using h
    have h' : (e.inv.left ≫ xa) ≫ t.ι.app a =
        (e.inv.left ≫ xb) ≫ t.ι.app b := by
      rw [Category.assoc, Category.assoc, hTop]
    obtain ⟨k, p, q, hpq⟩ := realizedHorn_stage_eq t ht hF (n + 1) idx
      (e.inv.left ≫ xa) (e.inv.left ≫ xb) h'
    have hback : xa ≫ hf.F.map p = xb ≫ hf.F.map q := by
      have e₁ : e.hom.left ≫ ((e.inv.left ≫ xa) ≫ hf.F.map p) =
          xa ≫ hf.F.map p := by
        rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
      have e₂ : e.hom.left ≫ ((e.inv.left ≫ xb) ≫ hf.F.map q) =
          xb ≫ hf.F.map q := by
        rw [← Category.assoc, ← Category.assoc, hleft, Category.id_comp]
      rw [← e₁, ← e₂, hpq]
    exact ⟨k, p, q, by simpa using hback⟩

/-- For every universe `u`, `realizedGeneratorCardinal.{u}` satisfies
`MorphismProperty.IsCardinalForSmallObjectArgument TopCat.realizedHornInclusions.{u}`. In a
relative horn-cell complex of this ordinal shape, morphisms out of a generator domain preserve
its colimit; the attaching families are small in the required universe. -/
instance : MorphismProperty.IsCardinalForSmallObjectArgument
    TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u} where
  preservesColimit i hi f hf :=
    preservesColimit_coyoneda_of_relativeCellComplex_horn.{u, u} i hi f hf
      (fun j hj => inferInstance)
