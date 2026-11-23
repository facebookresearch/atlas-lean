/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial
open SSet.FibrationSequence.Geometry

namespace MathlibExtTest.FibrationSequenceGroupFunctorsWholeSourceGroups

/-- All public roots belong to the whole actual producer module. -/
def expectedProducerRootsGroups : Array Lean.Name := #[
  (`SSet.FibrationSequence.Geometry).append
    `sequenceConnectingGroupHom,
  (`SSet.FibrationSequence.Geometry).append
    `sequenceConnectingGroupHom_apply,
  (`SSet.FibrationSequence.Geometry).append
    `totalGroupFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `baseGroupFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `fiberGroupFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `totalGroupFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `baseGroupFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `fiberGroupFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `projectionGroupNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `inclusionGroupNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `connectingGroupNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `projectionGroupNatTrans_apply,
  (`SSet.FibrationSequence.Geometry).append
    `inclusionGroupNatTrans_apply,
  (`SSet.FibrationSequence.Geometry).append
    `connectingGroupNatTrans_apply,
  (`SSet.FibrationSequence.Geometry).append
    `groupExact_at_base,
  (`SSet.FibrationSequence.Geometry).append
    `groupExact_at_fiber,
  (`SSet.FibrationSequence.Geometry).append
    `groupExact_at_total
]

#check @sequenceConnectingGroupHom
#print axioms sequenceConnectingGroupHom
#check @sequenceConnectingGroupHom_apply
#print axioms sequenceConnectingGroupHom_apply
#check @totalGroupFunctor
#print axioms totalGroupFunctor
#check @baseGroupFunctor
#print axioms baseGroupFunctor
#check @fiberGroupFunctor
#print axioms fiberGroupFunctor
#check @totalGroupFunctor_map
#print axioms totalGroupFunctor_map
#check @baseGroupFunctor_map
#print axioms baseGroupFunctor_map
#check @fiberGroupFunctor_map
#print axioms fiberGroupFunctor_map
#check @projectionGroupNatTrans
#print axioms projectionGroupNatTrans
#check @inclusionGroupNatTrans
#print axioms inclusionGroupNatTrans
#check @connectingGroupNatTrans
#print axioms connectingGroupNatTrans
#check @projectionGroupNatTrans_apply
#print axioms projectionGroupNatTrans_apply
#check @inclusionGroupNatTrans_apply
#print axioms inclusionGroupNatTrans_apply
#check @connectingGroupNatTrans_apply
#print axioms connectingGroupNatTrans_apply
#check @groupExact_at_base
#print axioms groupExact_at_base
#check @groupExact_at_fiber
#print axioms groupExact_at_fiber
#check @groupExact_at_total
#print axioms groupExact_at_total

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual whole chosen level fiber producer"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for n in expectedProducerRootsGroups do
    unless (env.find? n).isSome do throwError "missing original source root: {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong actual source owner: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedProducerRootsGroups.size}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors
#lint in MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors

end MathlibExtTest.FibrationSequenceGroupFunctorsWholeSourceGroups
