/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Code

/-!
# Axiom audit

`lake build Verify` fails if any declaration compiled in a `Code` module depends on an axiom
other than the three standard ones (`propext`, `Classical.choice`, `Quot.sound`). In particular
it fails on any `sorry`, since `sorry` elaborates to the axiom `sorryAx`.

The audit walks the declarations each module adds, rather than filtering by name, so private
declarations, auxiliary declarations and anything outside the `CDIS` namespace are covered too.
It also fails if it finds no module or no declaration, so a renamed library or namespace cannot
make it pass vacuously, and if a public declaration of the entry is outside namespace `CDIS`.
-/

open Lean Elab Command

/-- Audit every declaration of the `Code` modules and report how many were checked. -/
elab "#audit_code_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules : Nat := 0
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  let mut stray : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    unless (`Code).isPrefixOf moduleName do continue
    modules := modules + 1
    for name in env.header.moduleData[i]!.constNames do
      count := count + 1
      for ax in ← liftCoreM (collectAxioms name) do
        unless allowed.contains ax do
          bad := bad.push (name, ax)
      let userName := (privateToUserName? name).getD name
      unless userName.isInternal || (`CDIS).isPrefixOf userName do
        stray := stray.push name
  if modules == 0 || count == 0 then
    throwError m!"axiom audit found {modules} Code modules and {count} declarations"
  unless bad.isEmpty do
    throwError m!"non-standard axioms: {bad}"
  unless stray.isEmpty do
    throwError m!"declarations outside namespace CDIS: {stray}"
  logInfo m!"{count} declarations in {modules} Code modules audited: standard axioms only"

#audit_code_axioms
