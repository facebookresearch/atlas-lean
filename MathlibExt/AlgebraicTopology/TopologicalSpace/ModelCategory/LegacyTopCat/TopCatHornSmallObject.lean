/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornRelativeCellSmallness

/-!
# The small-object argument for realized horn inclusions

For each universe `u`, the realized horn inclusions in `TopCat.{u}` admit the small-object
argument, using `realizedGeneratorCardinal.{u}` and the colimit-smallness of each generator
domain along the corresponding relative cell complexes. The instance packages this cardinal
and its smallness conditions for the general factorization construction.
-/

@[expose] public section

universe u

open CategoryTheory

/-- In `TopCat.{u}`, the morphism property `realizedHornInclusions.{u}` has a small-object
argument. Its witnessing cardinal is `realizedGeneratorCardinal.{u}`, together with the
regularity, small generator-family, and relative-cell colimit-preservation conditions supplied
by the corresponding instances. -/
instance : MorphismProperty.HasSmallObjectArgument.{u}
    TopCat.realizedHornInclusions.{u} :=
  ⟨realizedGeneratorCardinal.{u}, inferInstance, inferInstance, inferInstance⟩
