/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions
import MathlibExtTest.AlgebraicTopology.ModelCategory.CofibrantGenerationLeftKanExtensionsTests
import Mathlib.Tactic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @HomotopicalAlgebra.CofibrantGenerationData.hasPointwiseLeftKanExtension
#print axioms HomotopicalAlgebra.CofibrantGenerationData.hasPointwiseLeftKanExtension
#check @HomotopicalAlgebra.CofibrantGenerationData.hasLeftKanExtension
#print axioms HomotopicalAlgebra.CofibrantGenerationData.hasLeftKanExtension

run_cmd do
  let env ← Lean.getEnv
  let groups := #[
    (`MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions, #[
      `HomotopicalAlgebra.CofibrantGenerationData.hasPointwiseLeftKanExtension,
      `HomotopicalAlgebra.CofibrantGenerationData.hasLeftKanExtension]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits, #[
      `HomotopicalAlgebra.CofibrantGenerationData.hasColimitsOfShape]),
    (`Mathlib.CategoryTheory.Comma.StructuredArrow.Small, #[
      `CategoryTheory.CostructuredArrow.essentiallySmall]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Pointwise, #[
      `CategoryTheory.Functor.pointwiseLeftKanExtension,
      `CategoryTheory.Functor.pointwiseLeftKanExtensionUnit,
      `CategoryTheory.Functor.pointwiseLeftKanExtensionIsUniversal]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction, #[
      `CategoryTheory.Functor.lanAdjunction])]
  for (moduleName, roots) in groups do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual module {moduleName}"
    for name in roots do
      let some actual := env.getModuleIdxFor? name
        | throwError m!"missing actual registration for {name}"
      if actual != expected then throwError m!"wrong source module for {name}"
      Lean.logInfo m!"GENERATION_LEFT_KAN_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"

#lint in MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions
