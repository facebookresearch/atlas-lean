/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

namespace MathlibExtTest.Algebra.Category.Grp.FilteredColimits.NatTail

open CategoryTheory CategoryTheory.Limits
universe v

/-- At positive offset one, the omitted initial source leg uses the actual first transition
before entering the first tail leg, for every group diagram and source element. -/
theorem positiveOffsetInitialLeg (D : ℕ ⥤ GrpCat.{v}) (x : D.obj 0) :
    (GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso D 1).inv
        ((GrpCat.FilteredColimits.colimitCocone D).ι.app 0 x) =
      (GrpCat.FilteredColimits.colimitCocone
        (CategoryTheory.NatTail.tailFunctor 1 ⋙ D)).ι.app 0
          (D.map (homOfLE (Nat.zero_le 1)) x) :=
  ConcreteCategory.congr_hom
    (GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι_all D 1 0) x

#print axioms positiveOffsetInitialLeg

#check
  @CategoryTheory.NatTail.tailFunctor
#print axioms
  CategoryTheory.NatTail.tailFunctor
#check
  @CategoryTheory.NatTail.tailFunctor_obj
#print axioms
  CategoryTheory.NatTail.tailFunctor_obj
#check
  @CategoryTheory.NatTail.tailFunctor_map
#print axioms
  CategoryTheory.NatTail.tailFunctor_map
#check
  @CategoryTheory.NatTail.tailFunctor_final
#print axioms
  CategoryTheory.NatTail.tailFunctor_final
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailDiagramFunctor
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailDiagramFunctor
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_pt
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_pt
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_ι
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_ι
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCoconeIsColimit
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCoconeIsColimit
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom_ι
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom_ι
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι_all
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι_all
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_naturality
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_naturality
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso_app
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso_app
#check
  @GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_naturality
#print axioms
  GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_naturality
/-- Every whole source declaration retains its actual kind and module. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  (`CategoryTheory.NatTail.tailFunctor, "def"),
  (`CategoryTheory.NatTail.tailFunctor_obj, "theorem"),
  (`CategoryTheory.NatTail.tailFunctor_map, "theorem"),
  (`CategoryTheory.NatTail.tailFunctor_final, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailDiagramFunctor, "def"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone, "def"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_pt, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCocone_ι, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailCoconeIsColimit, "def"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso, "def"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_hom_ι, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_ι_all, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_naturality, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso, "def"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailColimitNatIso_app, "theorem"),
  (`GrpCat.FilteredColimits.OriginalNatTailGeometry.tailComparisonIso_inv_naturality, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  unless expectedKernelKinds.size == 18 do
    throwError "Wrong complete current tail-root scope"
  let modules : Array Lean.Name := #[
    `MathlibExt.CategoryTheory.Filtered.NatTail,
    `MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail]
  for m in modules do
    let idx ← match env.getModuleIdx? m with
      | some i => pure i
      | none => throwError "Missing complete actual producer: {m}"
    let mut count : Nat := 0
    for (n, _) in env.constants do
      if env.getModuleIdxFor? n == some idx then
        count := count + 1
    unless count > 0 do
      throwError "Empty actual producer: {m}"
    Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count}"
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, expectedKind) in expectedKernelKinds do
    let m := if (`CategoryTheory.NatTail).isPrefixOf n then
      `MathlibExt.CategoryTheory.Filtered.NatTail
    else
      `MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
    let idx ← match env.getModuleIdx? m with
      | some i => pure i
      | none => throwError "Missing actual producer module: {m}"
    let info ← match env.find? n with
      | some c => pure c
      | none => throwError "Missing complete actual root: {n}"
    let (kind, body) ← match info with
      | .defnInfo d =>
        unless d.safety == Lean.DefinitionSafety.safe do
          throwError "Unsafe actual whole VALUE: {n}"
        pure ("def", d.value)
      | .thmInfo d => pure ("theorem", d.value)
      | _ => throwError "Wrong actual kernel kind: {n}"
    unless kind == expectedKind do
      throwError "Wrong actual kernel kind: {n} {kind}"
    if info.type.hasMVar || info.type.hasLooseBVars then
      throwError "Incomplete actual whole TYPE: {n}"
    if body.hasMVar || body.hasLooseBVars then
      throwError "Incomplete actual whole VALUE: {n}"
    let actualIdx ← match env.getModuleIdxFor? n with
      | some i => pure i
      | none => throwError "Missing actual root module index: {n}"
    unless actualIdx == idx do
      throwError "Wrong actual root membership: {n}"
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless allowed.contains a do
        throwError "Nonstandard actual root: {n} {a}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
    Lean.logInfo m!"KERNEL_KIND_MODULE {m} {n} KIND {kind} NUMERIC_MODULE {actualIdx.toNat}"
    Lean.logInfo m!"ACTUAL_WHOLE_TYPE_VALUE_BOUND {m} {n}"
    Lean.logInfo m!"ACTUAL_STD_ROOT {m} {n} AXIOMS {axs}"
  Lean.logInfo m!"EXPECTED_ROOTS {expectedKernelKinds.size}"

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
#lint in MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
#lint only unusedArguments in MathlibExt.CategoryTheory.Filtered.NatTail
#lint in MathlibExt.CategoryTheory.Filtered.NatTail
end MathlibExtTest.Algebra.Category.Grp.FilteredColimits.NatTail
