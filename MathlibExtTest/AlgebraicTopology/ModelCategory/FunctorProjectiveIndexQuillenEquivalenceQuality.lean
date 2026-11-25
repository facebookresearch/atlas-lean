/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexQuillenEquivalence
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorProjectiveIndexQuillenEquivalenceTests
import Mathlib.Tactic

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise
#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise
#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence
#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff
#check @HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff
#print axioms HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff

run_cmd do
  let env ← Lean.getEnv
  let groups := #[
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexQuillenEquivalence, #[
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise,
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise,
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes,
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence,
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff,
      `HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff]),
    (`MathlibExt.CategoryTheory.Functor.KanExtension.IndexAdjunctionProperties, #[
      `CategoryTheory.Functor.IndexAdjunctionProperties.homEquiv_property_iff,
      `CategoryTheory.Functor.IndexAdjunctionProperties.inverse_property_iff]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.KanExtensions, #[
      `HomotopicalAlgebra.FunctorProjective.KanExtensions.isQuillen_of_pointwise_right_classes]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions, #[
      `HomotopicalAlgebra.CofibrantGenerationData.hasLeftKanExtension]),
    (`Mathlib.CategoryTheory.EssentiallySmall, #[
      `CategoryTheory.locallySmall_of_faithful]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction, #[
      `CategoryTheory.Functor.lan,
      `CategoryTheory.Functor.lanAdjunction])]
  for (moduleName, roots) in groups do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual module {moduleName}"
    for name in roots do
      let some actual := env.getModuleIdxFor? name
        | throwError m!"missing actual registration for {name}"
      if actual != expected then throwError m!"wrong source module for {name}"
      Lean.logInfo m!"PROJECTIVE_INDEX_QE_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"

#lint in MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexQuillenEquivalence
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexQuillenEquivalence
