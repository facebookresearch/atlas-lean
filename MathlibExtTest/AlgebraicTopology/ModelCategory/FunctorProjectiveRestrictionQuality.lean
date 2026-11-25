/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorProjectiveRestrictionTests
import Mathlib.Tactic

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @HomotopicalAlgebra.FunctorProjective.Restriction.preserves_weakEquivalences_of_eqs
#print axioms HomotopicalAlgebra.FunctorProjective.Restriction.preserves_weakEquivalences_of_eqs
#check @HomotopicalAlgebra.FunctorProjective.Restriction.preserves_right_classes_of_eqs
#print axioms HomotopicalAlgebra.FunctorProjective.Restriction.preserves_right_classes_of_eqs
#check @HomotopicalAlgebra.FunctorProjective.Restriction.preserves_classes
#print axioms HomotopicalAlgebra.FunctorProjective.Restriction.preserves_classes

run_cmd do
  let env ← Lean.getEnv
  let groups := #[
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction, #[
      `HomotopicalAlgebra.FunctorProjective.Restriction.preserves_weakEquivalences_of_eqs,
      `HomotopicalAlgebra.FunctorProjective.Restriction.preserves_right_classes_of_eqs,
      `HomotopicalAlgebra.FunctorProjective.Restriction.preserves_classes]),
    (`MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.Restriction, #[
      `CategoryTheory.MorphismProperty.functorCategory_le_inverseImage_whiskeringLeft]),
    (`MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective, #[
      `HomotopicalAlgebra.FunctorProjective.modelCategory,
      `HomotopicalAlgebra.FunctorProjective.weakEquivalences_eq,
      `HomotopicalAlgebra.FunctorProjective.fibrations_eq,
      `HomotopicalAlgebra.FunctorProjective.trivialFibrations_eq])]
  for (moduleName, roots) in groups do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual module {moduleName}"
    for name in roots do
      let some actual := env.getModuleIdxFor? name
        | throwError m!"missing actual registration for {name}"
      if actual != expected then throwError m!"wrong source module for {name}"
      Lean.logInfo m!"PROJECTIVE_RESTRICTION_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"

#lint in MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
