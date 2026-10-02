/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Code

/-!
# Axiom audit

`lake build Verify` fails if any declaration in the `CDIS` namespace depends on an axiom
other than the three standard ones (`propext`, `Classical.choice`, `Quot.sound`). In particular
it fails on any `sorry`, since `sorry` elaborates to the axiom `sorryAx`.
-/

open Lean Elab Command

/-- Check every `CDIS.*` declaration and report how many were audited. -/
elab "#audit_cdis_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    if (`CDIS).isPrefixOf name && !name.isInternal then
      count := count + 1
      for ax in ← liftCoreM (collectAxioms name) do
        unless allowed.contains ax do
          bad := bad.push (name, ax)
  if bad.isEmpty then
    logInfo m!"{count} CDIS declarations audited: standard axioms only"
  else
    throwError m!"non-standard axioms: {bad}"

#audit_cdis_axioms
