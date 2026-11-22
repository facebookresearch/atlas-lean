/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObject
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Small-object factorization for the realized generator union

Packages small-object eligibility of the union of realized boundary and horn inclusions at the
realized-generator cardinal. The resulting statements describe its small-object argument and the
retract closure of its transfinite coproduct-pushout cells.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

/-- Small-object-argument package for the realized generator union. -/
instance : HasSmallObjectArgument.{u}
    (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u}) :=
  ⟨realizedGeneratorCardinal.{u}, inferInstance, inferInstance, inferInstance⟩

/-- Generic retract description for the generated left class. -/
theorem generatorUnion_llp_rlp :
    (TopCat.realizedBoundaryInclusions.{u} ⊔
      TopCat.realizedHornInclusions.{u}).rlp.llp =
      (transfiniteCompositions.{u}
        (coproducts.{u}
          (TopCat.realizedBoundaryInclusions.{u} ⊔
            TopCat.realizedHornInclusions.{u})).pushouts).retracts :=
  llp_rlp_of_hasSmallObjectArgument _
