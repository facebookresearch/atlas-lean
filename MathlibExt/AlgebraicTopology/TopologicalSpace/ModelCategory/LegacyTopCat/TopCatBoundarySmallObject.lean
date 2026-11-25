/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryRelativeCellSmallness

/-!
# Small-object-argument package for realized `TopCat` boundary inclusions

This file is part of the KQ3 layer. It supplies only the downstream
`HasSmallObjectArgument` package for `TopCat.realizedBoundaryInclusions`
at `realizedGeneratorCardinal`.

The `IsCardinalForSmallObjectArgument` instance is provided by
`TopCatBoundaryRelativeCellSmallness`; regularity and `OrderBot` come
from the presentability and structural inputs.
-/

@[expose] public section

universe u

open CategoryTheory

/-- Small-object-argument package for the realized boundary inclusions. -/
instance : MorphismProperty.HasSmallObjectArgument.{u}
    TopCat.realizedBoundaryInclusions.{u} :=
  ⟨realizedGeneratorCardinal.{u}, inferInstance, inferInstance, inferInstance⟩
