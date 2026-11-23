/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.JordanBlock
import all MathlibExt.LinearAlgebra.Matrix.JordanBlock
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import Mathlib.Tactic.Linter.Lint

/-! # Lightweight Jordan-block public clients and TYPE/DATA integrity -/

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.JordanBlock

open MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

universe u
variable {K : Type u} [Field K]

-- Preserve the original Atlas constructor-entry regressions.
example (μ : K) (s : ℕ) (i j : Fin s) :
    jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) :=
  jordanBlock_apply s μ i j

example (μ : K) : jordanBlock 2 μ (0 : Fin 2) (1 : Fin 2) = 1 := rfl

example (μ : K) : jordanBlock 2 μ (0 : Fin 2) (0 : Fin 2) = μ := rfl

example (μ : K) : jordanBlock 2 μ (1 : Fin 2) (0 : Fin 2) = 0 := rfl


/-- A public client reads every diagonal entry over the original arbitrary field. -/
theorem jordanBlock_diagonal (s : ℕ) (μ : K) (i : Fin s) :
    jordanBlock s μ i i = μ := by
  simp [jordanBlock_apply]

/-- The public block constructor includes its zero-dimensional matrix. -/
theorem jordanBlock_zero (μ : K) :
    jordanBlock 0 μ = (0 : Matrix (Fin 0) (Fin 0) K) := Subsingleton.elim _ _

/-- A public client distinguishes the superdiagonal from the subdiagonal for every eigenvalue. -/
theorem jordanBlock_finTwo_entries (μ : K) :
    jordanBlock 2 μ 0 0 = μ ∧ jordanBlock 2 μ 0 1 = 1 ∧
      jordanBlock 2 μ 1 0 = 0 ∧ jordanBlock 2 μ 1 1 = μ := by
  simp [jordanBlock_apply]

/-- Independent full original field-valued producer TYPE and literal DATA. -/
def expectedJordanBlock (s : ℕ) (μ : K) : Matrix (Fin s) (Fin s) K :=
  fun i j => if i.val + 1 = j.val then 1 else if i = j then μ else 0

/-- Independent full original characteristic TYPE and its reflexivity proof DATA. -/
theorem expectedJordanBlock_apply (s : ℕ) (μ : K) (i j : Fin s) :
    jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) := rfl

end MathlibExtTest.LinearAlgebra.Matrix.JordanBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Lean Elab Command Batteries.Tactic.Lint

run_cmd do
  let env := (← getEnv).setExporting false
  let src := `MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
  let fix := `MathlibExtTest.LinearAlgebra.Matrix.JordanBlock
  let pairs : Array (Name × Name) := #[
    (src ++ `jordanBlock, fix ++ `expectedJordanBlock),
    (src ++ `jordanBlock_apply, fix ++ `expectedJordanBlock_apply)]
  for (name, fixture) in pairs do
    let some actual := env.find? name | throwError "missing public Jordan-block declaration {name}"
    let some expected := env.find? fixture | throwError "missing full Jordan-block fixture {fixture}"
    let some av := actual.value? (allowOpaque := true) | throwError "missing canonical Jordan-block body {name}"
    let some ev := expected.value? (allowOpaque := true) | throwError "missing full Jordan-block fixture body"
    unless actual.levelParams.length == expected.levelParams.length do
      throwError "Jordan-block universe changed {name}"
    let levels := actual.levelParams.map Level.param
    let wanted := expected.type.instantiateLevelParams expected.levelParams levels
    unless (← liftTermElabM <| Meta.isDefEq actual.type wanted) do
      throwError "full Jordan-block TYPE changed {name}: actual {actual.type}; expected {wanted}"
    let body := ev.instantiateLevelParams expected.levelParams levels
    if ← liftTermElabM <| Meta.isProof av then
      -- Proof irrelevance makes definitional equality unsuitable for proof DATA.
      unless av.cleanupAnnotations == body.cleanupAnnotations do
        throwError "literal Jordan-block proof DATA changed {name}"
    else
      unless (← liftTermElabM <| Meta.isDefEq av body) do
        throwError "literal Jordan-block DATA changed {name}"
  let owned := pairs.map (·.1) ++ #[fix ++ `jordanBlock_diagonal,
    fix ++ `jordanBlock_zero, fix ++ `jordanBlock_finTwo_entries]
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo := owned
  let mut seen : NameSet := {}
  let mut projectCount : Nat := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "missing Jordan-block private dependency {name}"
    let axioms ← Lean.collectAxioms name
    unless axioms.all standard.contains do
      throwError "Jordan-block nonstandard axioms {name}: {axioms}"
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`MathlibExt, `MathlibExtTest].any
        (·.isPrefixOf env.header.moduleNames[idx.toNat]!) do continue
    projectCount := projectCount + (1 : Nat)
    if info.isUnsafe || info.isPartial || info.type.hasSorry || info.type.hasMVar ||
        info.type.hasFVar || info.type.hasLooseBVars then throwError "invalid Jordan-block TYPE {name}"
    for dep in info.type.getUsedConstants do todo := todo.push dep
    if let some value := info.value? (allowOpaque := true) then
      if value.hasSorry || value.hasMVar || value.hasFVar || value.hasLooseBVars then
        throwError "invalid Jordan-block DATA/proof {name}"
      for dep in value.getUsedConstants do todo := todo.push dep
    else
      match info with
      | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure ()
      | _ => throwError "missing Jordan-block private/project body {name}"
    if let .inductInfo d := info then for c in d.ctors do todo := todo.push c
  for name in owned do
    unless ((nolintAttr.getParam? env name).getD #[]).isEmpty do
      throwError "Jordan-block linter waiver {name}"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let checks := checks.map fun c => { c with test := fun n => Core.withCurrHeartbeats (c.test n) }
  let results ← liftCoreM <| lintCore owned checks (inIO := true)
  let errors : Nat := results.foldl (fun (n : Nat) r => n + r.2.size) (0 : Nat)
  let report ← liftCoreM <| formatLinterResults results owned (groupByFilename := true)
    "in lightweight canonical Jordan-block clients" (runSlowLinters := true) .medium checks.size
  logInfo report
  logInfo m!"JORDAN_BLOCK_FULL_TYPE_DATA_INTEGRITY {pairs.size} {pairs.size} {projectCount}"
  logInfo m!"JORDAN_BLOCK_STOCK_LINT {checks.size} {errors}"
  unless checks.size == (15 : Nat) && errors == (0 : Nat) do
    throwError "Jordan-block stock lint failed"
