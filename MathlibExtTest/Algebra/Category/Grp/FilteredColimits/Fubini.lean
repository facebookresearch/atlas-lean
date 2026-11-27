/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.Algebra.Category.Grp.FilteredColimits.Fubini
open GrpCat.FilteredColimits.Fubini

#check @innerColimitDiagram
#print axioms innerColimitDiagram
#check @iteratedColimitFunctor
#print axioms iteratedColimitFunctor
#check @jointLeg
#print axioms jointLeg
#check @jointLeg_naturality
#print axioms jointLeg_naturality
#check @jointCocone
#print axioms jointCocone
#check @CategoryTheory.Limits.coconeOfCoconeUncurry
#print axioms CategoryTheory.Limits.coconeOfCoconeUncurry
#check @CategoryTheory.Limits.IsColimit.ofCoconeUncurry
#print axioms CategoryTheory.Limits.IsColimit.ofCoconeUncurry
#check @jointCoconeIsColimit
#print axioms jointCoconeIsColimit
#check @transposedJointCocone
#print axioms transposedJointCocone
#check @transposedJointCocone_ι_app
#print axioms transposedJointCocone_ι_app
#check @transposedJointCoconeIsColimit
#print axioms transposedJointCoconeIsColimit
#check @fubiniIso
#print axioms fubiniIso
#check @fubiniIso_hom_leg
#print axioms fubiniIso_hom_leg
#check @fubiniIso_inv_leg
#print axioms fubiniIso_inv_leg
#check @fubiniIso_hom_apply
#print axioms fubiniIso_hom_apply
#check @fubiniIso_inv_apply
#print axioms fubiniIso_inv_apply
#check @iteratedColimit_map_fac
#print axioms iteratedColimit_map_fac
#check @fubiniIso_naturality
#print axioms fubiniIso_naturality
#check @fubiniNatIso
#print axioms fubiniNatIso
#check @fubiniNatIso_hom_app
#print axioms fubiniNatIso_hom_app
#check @fubiniNatIso_inv_app
#print axioms fubiniNatIso_inv_app
#check @fubiniNatIso_inv_naturality
#print axioms fubiniNatIso_inv_naturality

/-- Exact complete roots retain kernel kinds and actual module identity. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  ((`GrpCat.FilteredColimits.Fubini).append
    `innerColimitDiagram, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `iteratedColimitFunctor, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `jointLeg, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `jointLeg_naturality, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `jointCocone, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `jointCoconeIsColimit, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `transposedJointCocone, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `transposedJointCocone_ι_app, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `transposedJointCoconeIsColimit, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso_hom_leg, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso_inv_leg, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso_hom_apply, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso_inv_apply, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `iteratedColimit_map_fac, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniIso_naturality, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniNatIso, "def"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniNatIso_hom_app, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniNatIso_inv_app, "theorem"),
  ((`GrpCat.FilteredColimits.Fubini).append
    `fubiniNatIso_inv_naturality, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini
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

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini
#lint in MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini

end MathlibExtTest.Algebra.Category.Grp.FilteredColimits.Fubini
