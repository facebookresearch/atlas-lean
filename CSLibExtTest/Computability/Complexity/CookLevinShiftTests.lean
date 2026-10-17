/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Situation
public meta import CSLibExt.Computability.Complexity.CookLevin.Situation

/-! Tests for the Cook-Levin shift generator: run to halting on small instances, it leaves exactly
the encoded shift family on its output stack. The situation tables are checked against real runs
in `CookLevinSituationTests`. -/

namespace Cslib.Complexity.CookLevin.Tests

open Turing MetaMathlibExt Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-- Two label/state codes, one stack, two symbol codes, window depth one. -/
private def L0 : Family.Layout := ⟨2, 1, 2, 1⟩

-- One situation that pushes one symbol (code `1`) and consumes one: in-range shifts and the
-- pushed fill, no overflow fill.
#guard (runF (Shift.prog L0 (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => 1) 1)
      1000000 ⟨some (.pre .eg), false, CounterView.st (Shift.initF 1 2) []⟩).stk .out =
  encodeCNF (Shift.shFamily L0 (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => 1) 1 1 2)

-- Pure consumption (`pl = 0`, `cn = 1`): the overflow fill runs.
#guard (runF (Shift.prog L0 (fun _ => 1) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ _ => 0) 1)
      1000000 ⟨some (.pre .eg), false, CounterView.st (Shift.initF 1 2) []⟩).stk .out =
  encodeCNF (Shift.shFamily L0 (fun _ => 1) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ _ => 0) 1 1 2)

-- Two situations and two steps; the family is nonempty.
#guard (Shift.shFamily L0 (fun i => i % 2) (fun i _ => i % 2) (fun _ _ => 0) (fun _ _ _ => 1)
    2 2 2).length > 0

#guard (runF (Shift.prog L0 (fun i => i % 2) (fun i _ => i % 2) (fun _ _ => 0) (fun _ _ _ => 1) 2)
      1000000 ⟨some (.pre .eg), false, CounterView.st (Shift.initF 2 2) [false]⟩).stk .out =
  encodeCNF (Shift.shFamily L0 (fun i => i % 2) (fun i _ => i % 2) (fun _ _ => 0)
    (fun _ _ _ => 1) 2 2 2) ++ [false]

end Cslib.Complexity.CookLevin.Tests
