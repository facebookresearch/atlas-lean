/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornRelativeCellSmallness

/-!
# Small-object instance for realized horns in `TopCat`

This file is part of the KQ3 layer. It supplies only the downstream
`HasSmallObjectArgument` package for `TopCat.realizedHornInclusions` at
`realizedGeneratorCardinal`, reusing the staged horn
`IsCardinalForSmallObjectArgument` instance. The relative-cell theorem and
the cardinal instance live in the staged provider and are not duplicated
here. No factorization data, weak factorization system, boundary or union
case, or model-category claim is made here.
-/

@[expose] public section

universe u

open CategoryTheory

/-- Small-object-argument package for realized horns. -/
instance : MorphismProperty.HasSmallObjectArgument.{u}
    TopCat.realizedHornInclusions.{u} :=
  ⟨realizedGeneratorCardinal.{u}, inferInstance, inferInstance, inferInstance⟩
