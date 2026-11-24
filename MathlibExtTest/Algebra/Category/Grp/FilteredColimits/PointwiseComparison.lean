/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
open GrpCat.FilteredColimits.PointwiseComparison

#check @evaluatedCocone
#print axioms evaluatedCocone
#check @pointwiseDesc
#print axioms pointwiseDesc
#check @pointwiseDesc_fac
#print axioms pointwiseDesc_fac
#check @pointwiseComparison
#print axioms pointwiseComparison
#check @mappedGroupCocone
#print axioms mappedGroupCocone
#check @groupCoconeComparisonDesc
#print axioms groupCoconeComparisonDesc
#check @groupCoconeComparisonDesc_fac
#print axioms groupCoconeComparisonDesc_fac
#check @groupCoconeComparisonDesc_joint_fac
#print axioms groupCoconeComparisonDesc_joint_fac
#check @fubini_pointwise_joint_fac
#print axioms fubini_pointwise_joint_fac
#check @groupCoconeComparisonDesc_fubini_word
#print axioms groupCoconeComparisonDesc_fubini_word
#check @groupCoconeComparisonIso
#print axioms groupCoconeComparisonIso
#check @groupCoconeComparisonIso_hom
#print axioms groupCoconeComparisonIso_hom
#check @groupCoconeComparisonIso_inv
#print axioms groupCoconeComparisonIso_inv
#check @pointwiseComparison_map_square
#print axioms pointwiseComparison_map_square
#check @groupCoconeComparisonDesc_map_square
#print axioms groupCoconeComparisonDesc_map_square

/-- Exact complete roots retain kernel kinds and actual module identity. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `evaluatedCocone, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `pointwiseDesc, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `pointwiseDesc_fac, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `pointwiseComparison, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `mappedGroupCocone, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonDesc, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonDesc_fac, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonDesc_joint_fac, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `fubini_pointwise_joint_fac, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonDesc_fubini_word, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonIso, "def"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonIso_hom, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonIso_inv, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `pointwiseComparison_map_square, "theorem"),
  ((`GrpCat.FilteredColimits.PointwiseComparison).append
    `groupCoconeComparisonDesc_map_square, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
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

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
#lint in MathlibExt.Algebra.Category.Grp.FilteredColimits.PointwiseComparison

end MathlibExtTest.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
