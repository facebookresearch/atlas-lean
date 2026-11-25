/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorInjectiveIndexQuillenEquivalenceTests
import Mathlib.Tactic

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise
#print axioms HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise
#check @HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise
#print axioms HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise
#check @HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
#print axioms HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes

run_cmd do
  let env ← Lean.getEnv
  let groups := #[
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence, #[
      `HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise,
      `HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise,
      `HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes]),
    (`MathlibExt.CategoryTheory.Functor.KanExtension.RightIndexAdjunctionProperties, #[
      `CategoryTheory.Functor.RightIndexAdjunctionProperties.homEquiv_property_iff,
      `CategoryTheory.Functor.RightIndexAdjunctionProperties.inverse_property_iff]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions, #[
      `HomotopicalAlgebra.FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence, #[
      `CategoryTheory.Adjunction.IsQuillenEquivalence]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction, #[
      `CategoryTheory.Functor.ran,
      `CategoryTheory.Functor.ranAdjunction])]
  for (moduleName, roots) in groups do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual module {moduleName}"
    for name in roots do
      let some actual := env.getModuleIdxFor? name
        | throwError m!"missing actual registration for {name}"
      if actual != expected then throwError m!"wrong source module for {name}"
      Lean.logInfo m!"RAN_INDEX_QE_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"

#lint in MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence
