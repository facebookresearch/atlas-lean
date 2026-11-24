/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.Presentable.LiftingTest
import all MathlibExtTest.CategoryTheory.Presentable.LiftingTestTests
import all MathlibExtTest.CategoryTheory.Presentable.LiftingTestOwner
import all MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
import all MathlibExtTest.CategoryTheory.NatTrans.PointwiseArrowAccessibilityOwner
import Mathlib.Tactic
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

run_cmd do
  let env ← Lean.getEnv
  let modules := #[
    `MathlibExt.CategoryTheory.Presentable.LiftingTest,
    `MathlibExtTest.CategoryTheory.Presentable.LiftingTestTests,
    `MathlibExtTest.CategoryTheory.Presentable.LiftingTestOwner,
    `MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation,
    `MathlibExtTest.CategoryTheory.NatTrans.PointwiseArrowAccessibilityOwner]
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let mut total : Nat := 0
  for moduleName in modules do
    let some expected := env.getModuleIdx? moduleName
      | throwError m!"missing actual preservation module {moduleName}"
    let names := env.constants.toList.filterMap fun entry =>
      if env.getModuleIdxFor? entry.1 == some expected then some entry.1 else none
    let names := names.toArray.qsort Lean.Name.lt
    if names.isEmpty then throwError m!"selected preservation module has no constants {moduleName}"
    for name in names do
      let some info := env.find? name | throwError m!"missing actual constant {name}"
      if info.isUnsafe then throwError m!"unsafe preservation constant {name}"
      let actualName ← Lean.Elab.Command.liftTermElabM do
        let term ← Lean.Elab.Term.elabTerm (← `(term| @$(Lean.mkIdent name))) none
        pure term.getAppFn.constName!
      if actualName != name then throwError m!"wrong resolved preservation constant {name}"
      let some actual := env.getModuleIdxFor? actualName
        | throwError m!"missing actual preservation source role {actualName}"
      if actual != expected then throwError m!"wrong actual preservation module {actualName}"
      Lean.logInfo m!"PRESERVATION_READABLE_TYPE {name}\n{info.type}"
      Lean.logInfo m!"PRESERVATION_LOSSLESS_TYPE {name} LEVELS {reprStr info.levelParams}\n{reprStr info.type}"
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        if !standard.contains axiomName then
          throwError m!"nonstandard preservation axiom in {name}: {axiomName}"
      Lean.logInfo m!"PRESERVATION_STANDARD_AXIOMS {name} {axioms}"
      Lean.logInfo m!"PRESERVATION_SOURCE_ROLE {name} EXPECTED {expected.toNat} ACTUAL {actual.toNat}"
    total := total + names.size
    Lean.logInfo m!"PRESERVATION_WHOLE_MODULE {moduleName} CONSTANTS {names.size}"
  Lean.logInfo m!"PRESERVATION_WHOLE_TOTAL {total}"

#lint in MathlibExt.CategoryTheory.Presentable.LiftingTest
#lint only unusedArguments in MathlibExt.CategoryTheory.Presentable.LiftingTest
#lint in MathlibExtTest.CategoryTheory.Presentable.LiftingTestTests
#lint only unusedArguments in MathlibExtTest.CategoryTheory.Presentable.LiftingTestTests
#lint in MathlibExtTest.CategoryTheory.Presentable.LiftingTestOwner
#lint only unusedArguments in MathlibExtTest.CategoryTheory.Presentable.LiftingTestOwner
#lint in MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
#lint only unusedArguments in MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
#lint in MathlibExtTest.CategoryTheory.NatTrans.PointwiseArrowAccessibilityOwner
#lint only unusedArguments in MathlibExtTest.CategoryTheory.NatTrans.PointwiseArrowAccessibilityOwner
