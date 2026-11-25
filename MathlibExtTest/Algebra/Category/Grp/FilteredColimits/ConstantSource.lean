/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.Algebra.Category.Grp.FilteredColimits.ConstantSource
open GrpCat.FilteredColimits.ConstantSource

#check @zeroTo
#print axioms zeroTo
#check @zeroTo_zero
#print axioms zeroTo_zero
#check @zeroTo_comp
#print axioms zeroTo_comp
#check @map_zeroTo_isIso
#print axioms map_zeroTo_isIso
#check @zeroMapInverse
#print axioms zeroMapInverse
#check @zeroMapInverse_hom_id
#print axioms zeroMapInverse_hom_id
#check @zeroMapInverse_id_hom
#print axioms zeroMapInverse_id_hom
#check @zeroMapInverse_zero
#print axioms zeroMapInverse_zero
#check @constantSourceCocone
#print axioms constantSourceCocone
#check @constantSourceCoconeIsColimit
#print axioms constantSourceCoconeIsColimit
#check @constantSourceColimitIso
#print axioms constantSourceColimitIso
#check @constantSourceColimitIso_hom
#print axioms constantSourceColimitIso_hom
#check @constantSourceColimitIso_inv
#print axioms constantSourceColimitIso_inv
#check @constantSourceColimitIso_inv_leg
#print axioms constantSourceColimitIso_inv_leg
#check @constantSource_zero_leg_isIso
#print axioms constantSource_zero_leg_isIso
#check @constantSourceColimitIso_hom_naturality
#print axioms constantSourceColimitIso_hom_naturality
#check @constantSourceColimitIso_inv_naturality
#print axioms constantSourceColimitIso_inv_naturality

/-- Exact complete roots retain kernel kinds and actual module identity. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroTo, "def"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroTo_zero, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroTo_comp, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `map_zeroTo_isIso, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroMapInverse, "def"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroMapInverse_hom_id, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroMapInverse_id_hom, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `zeroMapInverse_zero, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceCocone, "def"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceCoconeIsColimit, "def"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso, "def"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso_hom, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso_inv, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso_inv_leg, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSource_zero_leg_isIso, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso_hom_naturality, "theorem"),
  ((`GrpCat.FilteredColimits.ConstantSource).append
    `constantSourceColimitIso_inv_naturality, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual original producer module"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for (n, expectedKind) in expectedKernelKinds do
    let info ← match env.find? n with
      | some c => pure c
      | none => throwError "missing actual original root: {n}"
    let kind := match info with
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | _ => "other"
    unless kind == expectedKind do throwError "wrong actual kernel kind: {n} {kind}"
    let actualIdx ← match env.getModuleIdxFor? n with
      | some i => pure i
      | none => throwError "missing actual numeric root module: {n}"
    unless actualIdx == idx do throwError "wrong actual original producer membership: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
    Lean.logInfo m!"KERNEL_KIND_MODULE {m} {n} KIND {kind} NUMERIC_MODULE {actualIdx.toNat}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedKernelKinds.size}"

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource
#lint in MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource

end MathlibExtTest.Algebra.Category.Grp.FilteredColimits.ConstantSource
