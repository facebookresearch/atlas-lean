/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SSet.LoopShiftOriginalGeometry

namespace MathlibExtTest.LoopConnectingHomotopyWholeSource

example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    SSet.KanComplex (SSet.loopSpace X x) := inferInstance

example (n : ℕ) (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    Group (SSet.KanComplex.π (n + 1) (SSet.loopSpace X x) (originalLoopPoint X x)) :=
  inferInstance

/-- All public roots belong to the whole actual producer module. -/
def expectedProducerRoots : Array Lean.Name := #[
  (`SSet.LoopShiftOriginalGeometry).append
    `originalLoopPoint,
  (`SSet.LoopShiftOriginalGeometry).append
    `originalLoopPoint_eq,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_apply,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_one,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_symm_one,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_naturality,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_naturality_function,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_symm_naturality,
  (`SSet.LoopShiftOriginalGeometry).append
    `loopConnectingEquiv_positive
]

#check @originalLoopPoint
#print axioms originalLoopPoint
#check @originalLoopPoint_eq
#print axioms originalLoopPoint_eq
#check @loopConnectingEquiv
#print axioms loopConnectingEquiv
#check @loopConnectingEquiv_apply
#print axioms loopConnectingEquiv_apply
#check @loopConnectingEquiv_one
#print axioms loopConnectingEquiv_one
#check @loopConnectingEquiv_symm_one
#print axioms loopConnectingEquiv_symm_one
#check @loopConnectingEquiv_naturality
#print axioms loopConnectingEquiv_naturality
#check @loopConnectingEquiv_naturality_function
#print axioms loopConnectingEquiv_naturality_function
#check @loopConnectingEquiv_symm_naturality
#print axioms loopConnectingEquiv_symm_naturality
#check @loopConnectingEquiv_positive
#print axioms loopConnectingEquiv_positive

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual whole chosen level fiber producer"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for n in expectedProducerRoots do
    unless (env.find? n).isSome do throwError "missing original source root: {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong actual source owner: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedProducerRoots.size}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
#lint in MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy

end MathlibExtTest.LoopConnectingHomotopyWholeSource
