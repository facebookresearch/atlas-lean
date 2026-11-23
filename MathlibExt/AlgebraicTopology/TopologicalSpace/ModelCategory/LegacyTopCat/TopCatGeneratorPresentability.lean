/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedGeneratorCardinal
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Smallness inputs for realized TopCat generators

This file is part of the KQ3 layer. It banks the checkable cardinal and
smallness inputs for the realized generator program at
`realizedGeneratorCardinal`:

* the underlying types of the realized boundaries and
  horns satisfy `HasCardinalLT` at `realizedGeneratorCardinal`, hence are
  `IsCardinalPresentable` in `Type`;
* the families `TopCat.realizedBoundaryInclusions` and
  `TopCat.realizedHornInclusions` are `MorphismProperty.IsSmall`.

Companion inputs proved elsewhere: the `Cardinal.mk` bounds in
`RealizedGeneratorCardinal`, and the generator families with their
closed-`T1` bounds in `TopCatGenerators`
(`realizedBoundaryInclusions_le_closedT1Embeddings`,
`realizedHornInclusions_le_closedT1Embeddings`).

This is not a `TopCat`-level presentability claim, not an
`IsCardinalForSmallObjectArgument` instance, and not a small-object,
factorization, cofibration, weak-equivalence, or model-category claim. No
`TopCat`-level presentability theorem is claimed or currently needed: the
`Type`-level presentability banked here combines with stage
factorization/equality through the colimit-preserving forgetful functor in
`TopCatGeneratorFilteredFactorization` and `TopCatGeneratorStageEq`,
caller-specific preservation in the boundary/horn relative-cell smallness
modules, and the larger cell-universe closed-embedding Small bridge, and the
relative-cell route supplies the small-object instances at
`realizedGeneratorCardinal`.
-/

@[expose] public section

open scoped Simplicial

universe u

/-- The generator bound is regular, installed locally for presentability. -/
instance : Fact realizedGeneratorCardinal.{u}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal.{u}⟩

/-- Realized boundaries satisfy the generator cardinal bound. -/
theorem hasCardinalLT_realizedBoundary (n : ℕ) :
    HasCardinalLT ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt (mk_realizedBoundary_le n) (Order.lt_succ _)

/-- Realized horns satisfy the generator cardinal bound. -/
theorem hasCardinalLT_realizedHorn (n : ℕ) (i : Fin (n + 1)) :
    HasCardinalLT ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt (mk_realizedHorn_le n i) (Order.lt_succ _)

/-- Realized boundaries are presentable in `Type` at the bound. -/
theorem isCardinalPresentable_realizedBoundary (n : ℕ) :
    CategoryTheory.IsCardinalPresentable
      ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} :=
  (hasCardinalLT_realizedBoundary n).isCardinalPresentable

/-- Realized horns are presentable in `Type` at the bound. -/
theorem isCardinalPresentable_realizedHorn (n : ℕ) (i : Fin (n + 1)) :
    CategoryTheory.IsCardinalPresentable
      ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} :=
  (hasCardinalLT_realizedHorn n i).isCardinalPresentable

/-- The realized boundary inclusion family is small. -/
instance : CategoryTheory.MorphismProperty.IsSmall.{u}
    TopCat.realizedBoundaryInclusions.{u} :=
  CategoryTheory.MorphismProperty.isSmall_ofHoms _

/-- The realized horn inclusion family is small. -/
instance : CategoryTheory.MorphismProperty.IsSmall.{u}
    TopCat.realizedHornInclusions.{u} := by
  have hNat : Small.{u} ℕ := small_zero ℕ
  have hFin : ∀ n : ℕ, Small.{u} (Fin (n + 2)) := fun n => small_zero _
  have hInner : ∀ n : ℕ, CategoryTheory.MorphismProperty.IsSmall.{u}
      (CategoryTheory.MorphismProperty.ofHoms (fun i : Fin (n + 2) =>
        SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι)) :=
    fun n => @CategoryTheory.MorphismProperty.isSmall_ofHoms _ _ _ (hFin n) _ _ _
  unfold TopCat.realizedHornInclusions
  exact @CategoryTheory.MorphismProperty.isSmall_iSup _ _ _ _ hNat hInner
