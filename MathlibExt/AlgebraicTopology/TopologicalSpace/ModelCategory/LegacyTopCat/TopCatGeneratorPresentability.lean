/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedGeneratorCardinal
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Cardinal bounds of realized boundary and horn types

The underlying types of realized simplicial boundaries and horns have
cardinality smaller than the regular realized-generator cardinal `κ`, and are
therefore `κ`-presentable as objects of the category of types. The realized
boundary and horn morphism families are small in the space universe.

These are type-level presentability statements. The corresponding topological
stage factorization uses the separate closed-embedding hypotheses on diagrams.
-/

@[expose] public section

open scoped Simplicial

universe u

/--
The realized-generator cardinal is regular.
-/
instance : Fact realizedGeneratorCardinal.{u}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal.{u}⟩

/--
The underlying type of a realized simplicial boundary has cardinality strictly
smaller than the realized-generator cardinal.
-/
theorem hasCardinalLT_realizedBoundary (n : ℕ) :
    HasCardinalLT ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt (mk_realizedBoundary_le n) (Order.lt_succ _)

/--
The underlying type of a realized simplicial horn has cardinality strictly
smaller than the realized-generator cardinal.
-/
theorem hasCardinalLT_realizedHorn (n : ℕ) (i : Fin (n + 1)) :
    HasCardinalLT ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt (mk_realizedHorn_le n i) (Order.lt_succ _)

/--
The underlying type of a realized boundary is presentable at the
realized-generator cardinal in the category of types.
-/
theorem isCardinalPresentable_realizedBoundary (n : ℕ) :
    CategoryTheory.IsCardinalPresentable
      ↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))
      realizedGeneratorCardinal.{u} :=
  (hasCardinalLT_realizedBoundary n).isCardinalPresentable

/--
The underlying type of a realized horn is presentable at the
realized-generator cardinal in the category of types.
-/
theorem isCardinalPresentable_realizedHorn (n : ℕ) (i : Fin (n + 1)) :
    CategoryTheory.IsCardinalPresentable
      ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))
      realizedGeneratorCardinal.{u} :=
  (hasCardinalLT_realizedHorn n i).isCardinalPresentable

/--
The family of realized simplicial boundary inclusions is small in the
space universe.
-/
instance : CategoryTheory.MorphismProperty.IsSmall.{u}
    TopCat.realizedBoundaryInclusions.{u} :=
  CategoryTheory.MorphismProperty.isSmall_ofHoms _

/--
The family of realized simplicial horn inclusions is small in the
space universe.
-/
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
