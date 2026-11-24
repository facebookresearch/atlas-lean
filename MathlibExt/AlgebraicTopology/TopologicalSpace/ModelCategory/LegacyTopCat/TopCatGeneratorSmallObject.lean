/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObjectInputs
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorRelativeCellSmallness

/-!
# Small-object cardinal for realized topological generators

The union `TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`
admits `IsCardinalForSmallObjectArgument` at `realizedGeneratorCardinal`.
The presentability and structural inputs supply regularity, smallness and the
ordinal bottom, while the relative-cell smallness theorem supplies the
source-Hom colimit-preservation field.
-/

@[expose] public section

universe u

open CategoryTheory

/-- Small-object cardinal instance for the realized generator union. -/
instance : MorphismProperty.IsCardinalForSmallObjectArgument
    (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u})
    realizedGeneratorCardinal.{u} where
  preservesColimit i hi f hf :=
    preservesColimit_coyoneda_of_relativeCellComplex_generators.{u, u} i hi f hf
      (fun j hj => inferInstance)
