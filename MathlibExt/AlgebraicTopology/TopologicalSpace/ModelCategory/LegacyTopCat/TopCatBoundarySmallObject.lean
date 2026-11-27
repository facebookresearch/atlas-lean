/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryRelativeCellSmallness

/-!
# Small object argument for realized boundary inclusions

The family of realized simplicial boundary inclusions in topological spaces
admits the small object argument at the realized-generator cardinal. The
cardinal's regularity and ordinal bottom element combine with relative-cell
colimit smallness to supply this structure.
-/

@[expose] public section

universe u

open CategoryTheory

/--
The realized-boundary inclusion family admits a small object argument, using
the realized-generator cardinal and its relative-cell smallness.
-/
instance : MorphismProperty.HasSmallObjectArgument.{u}
    TopCat.realizedBoundaryInclusions.{u} :=
  ⟨realizedGeneratorCardinal.{u}, inferInstance, inferInstance, inferInstance⟩
