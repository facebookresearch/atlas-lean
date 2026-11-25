/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace
  MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction

example : (λ_ PointedCGWH.IntervalCoefficient.interval.{u, v}).inv ≫
    (PointedCGWH.freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
      PointedCGWH.RealizedIntervalContraction.action =
    PointedCGWH.IntervalCoefficient.augmentation ≫ PointedCGWH.IntervalCoefficient.endpoint 0 :=
  PointedCGWH.RealizedIntervalContraction.action_one

example (t : unitInterval) (p : CGWH.point.{u, v}) :
    CGWH.RealizedIntervalContraction.homotopy.{u, v} (t, CGWH.intervalOne.{u, v} p) =
      CGWH.intervalOne p :=
  CGWH.RealizedIntervalContraction.homotopy_fixed.{u, v} t p

#check @CGWH.RealizedIntervalContraction.pointToUnit
#print axioms CGWH.RealizedIntervalContraction.pointToUnit
#check @CGWH.RealizedIntervalContraction.intervalOne_eq
#print axioms CGWH.RealizedIntervalContraction.intervalOne_eq
#check @CGWH.RealizedIntervalContraction.intervalOne_coordinate
#print axioms CGWH.RealizedIntervalContraction.intervalOne_coordinate
#check @CGWH.RealizedIntervalContraction.homotopy
#print axioms CGWH.RealizedIntervalContraction.homotopy
#check @CGWH.RealizedIntervalContraction.homotopy_fixed
#print axioms CGWH.RealizedIntervalContraction.homotopy_fixed
#check @CGWH.RealizedIntervalContraction.action
#print axioms CGWH.RealizedIntervalContraction.action
#check @CGWH.RealizedIntervalContraction.action_zero
#print axioms CGWH.RealizedIntervalContraction.action_zero
#check @CGWH.RealizedIntervalContraction.action_one
#print axioms CGWH.RealizedIntervalContraction.action_one
#check @CGWH.RealizedIntervalContraction.action_fixed
#print axioms CGWH.RealizedIntervalContraction.action_fixed
#check @PointedCGWH.RealizedIntervalContraction.zeroSimplexIsoPoint_eq
#print axioms PointedCGWH.RealizedIntervalContraction.zeroSimplexIsoPoint_eq
#check @PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq
#print axioms PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq
#check @PointedCGWH.RealizedIntervalContraction.endpoint_one_eq
#print axioms PointedCGWH.RealizedIntervalContraction.endpoint_one_eq
#check @PointedCGWH.RealizedIntervalContraction.augmentation_eq
#print axioms PointedCGWH.RealizedIntervalContraction.augmentation_eq
#check @PointedCGWH.RealizedIntervalContraction.time
#print axioms PointedCGWH.RealizedIntervalContraction.time
#check @PointedCGWH.RealizedIntervalContraction.action
#print axioms PointedCGWH.RealizedIntervalContraction.action
#check @PointedCGWH.RealizedIntervalContraction.action_zero
#print axioms PointedCGWH.RealizedIntervalContraction.action_zero
#check @PointedCGWH.RealizedIntervalContraction.action_one
#print axioms PointedCGWH.RealizedIntervalContraction.action_one
#check @PointedCGWH.RealizedIntervalContraction.action_fixed
#print axioms PointedCGWH.RealizedIntervalContraction.action_fixed

/-- Every whole original contraction and endpoint root belongs to the true producer. -/
def expectedProducerRoots : Array Lean.Name := #[
  `CGWH.RealizedIntervalContraction.pointToUnit,
  `CGWH.RealizedIntervalContraction.intervalOne_eq,
  `CGWH.RealizedIntervalContraction.intervalOne_coordinate,
  `CGWH.RealizedIntervalContraction.homotopy,
  `CGWH.RealizedIntervalContraction.homotopy_fixed,
  `CGWH.RealizedIntervalContraction.action,
  `CGWH.RealizedIntervalContraction.action_zero,
  `CGWH.RealizedIntervalContraction.action_one,
  `CGWH.RealizedIntervalContraction.action_fixed,
  `PointedCGWH.RealizedIntervalContraction.zeroSimplexIsoPoint_eq,
  `PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq,
  `PointedCGWH.RealizedIntervalContraction.endpoint_one_eq,
  `PointedCGWH.RealizedIntervalContraction.augmentation_eq,
  `PointedCGWH.RealizedIntervalContraction.time,
  `PointedCGWH.RealizedIntervalContraction.action,
  `PointedCGWH.RealizedIntervalContraction.action_zero,
  `PointedCGWH.RealizedIntervalContraction.action_one,
  `PointedCGWH.RealizedIntervalContraction.action_fixed
]

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing producer module"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero producer declarations"
  for n in expectedProducerRoots do
    unless (env.find? n).isSome do throwError "missing root: {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong root module: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedProducerRoots.size}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
#lint in MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
