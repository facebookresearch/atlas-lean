/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean

/-!
# Fixtures for the `atlas_audit` axiom / sorry classifier

Self-contained: defines a genuinely proved theorem and a `sorry`-backed one,
then asserts the kernel's transitive-axiom traversal labels each correctly.
Imports only `Lean`, so it runs without building Mathlib or Atlas:

```bash
lake env lean Audit/Test.lean
```
-/

open Lean

theorem auditFixtureProved : True := trivial
theorem auditFixtureSorry : True := by sorry

private def sorryAxiom : Name := `sorryAx

private def axiomsOf (env : Environment) (c : Name) : Array Name :=
  let (_, s) := ((Lean.CollectAxioms.collect c).run env).run {}
  s.axioms

run_cmd do
  let env ← getEnv
  let provedAxs := axiomsOf env `auditFixtureProved
  let sorryAxs := axiomsOf env `auditFixtureSorry
  unless !provedAxs.contains sorryAxiom do
    throwError "fixture: a genuinely proved theorem must not reach sorryAx"
  unless sorryAxs.contains sorryAxiom do
    throwError "fixture: a sorry-backed theorem must reach sorryAx"
  logInfo "atlas_audit classifier fixtures pass"
