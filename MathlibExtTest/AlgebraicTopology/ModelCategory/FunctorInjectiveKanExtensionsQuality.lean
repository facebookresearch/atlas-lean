/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorInjectiveKanExtensionsTests
import Mathlib.Tactic

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @HomotopicalAlgebra.FunctorInjective.KanExtensions.preserves_left_classes_of_eqs
#print axioms HomotopicalAlgebra.FunctorInjective.KanExtensions.preserves_left_classes_of_eqs
#check @HomotopicalAlgebra.FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes
#print axioms HomotopicalAlgebra.FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes

run_cmd do
  let env ← Lean.getEnv
  let groups := #[
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions, #[
      `HomotopicalAlgebra.FunctorInjective.KanExtensions.preserves_left_classes_of_eqs,
      `HomotopicalAlgebra.FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes]),
    (`MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorInjectiveKanExtensionsTests, #[
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "MathlibExtTest") "AlgebraicTopology") "ModelCategory") "FunctorInjectiveKanExtensionsTests") 0) "MathlibExtTest") "FunctorInjectiveKanExtensions") "nativeIndexProjectionMap"),
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "MathlibExtTest") "AlgebraicTopology") "ModelCategory") "FunctorInjectiveKanExtensionsTests") 0) "MathlibExtTest") "FunctorInjectiveKanExtensions") "nativeCoefficientProjectionMap")]),
    (`MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.Restriction, #[
      `CategoryTheory.MorphismProperty.functorCategory_le_inverseImage_whiskeringLeft]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction, #[
      `CategoryTheory.Functor.ran,
      `CategoryTheory.Functor.ranAdjunction,
      `CategoryTheory.Functor.ranObjObjIsoLimit]),
    (`Mathlib.CategoryTheory.Functor.KanExtension.Pointwise, #[
      `CategoryTheory.Functor.HasPointwiseRightKanExtension]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction, #[
      `CategoryTheory.Adjunction.IsQuillenAdjunction])]
  for (moduleName, roots) in groups do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual module {moduleName}"
    for name in roots do
      let some actual := env.getModuleIdxFor? name
        | throwError m!"missing actual registration for {name}"
      if actual != expected then throwError m!"wrong source module for {name}"
      Lean.logInfo m!"RAN_QUILLEN_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"

#lint in MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions
