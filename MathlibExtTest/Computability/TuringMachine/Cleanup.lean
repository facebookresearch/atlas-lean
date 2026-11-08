/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Cleanup
public meta import MathlibExt.Computability.TuringMachine.Cleanup

/-! Tests for the stack cleanup. -/

namespace MetaMathlibExt.TM2Program.CleanupTests

open Turing

/-- Three stacks of naturals; labels `0` (cleanup) and `1` (halt). -/
private def M : Fin 2 → TM2.Stmt (fun _ : Fin 3 => ℕ) (Fin 2) Bool
  | 0 => cleanS [0, 1] 0 1
  | 1 => .halt

/-- Step with fuel until halting; also count the steps. -/
private def runF : ℕ → TM2.Cfg (fun _ : Fin 3 => ℕ) (Fin 2) Bool × ℕ →
    TM2.Cfg (fun _ : Fin 3 => ℕ) (Fin 2) Bool × ℕ
  | 0, c => c
  | n + 1, (c, i) => if c.l = some 1 then (c, i) else
    match TM2.step M c with
    | some c' => runF n (c', i + 1)
    | none => (c, i)

private def S₀ : ∀ _ : Fin 3, List ℕ := fun k => [[1, 2, 3], [4], [5, 6]][k]

private def out := runF 10 (⟨some 0, true, S₀⟩, 0)

-- Stacks `0` and `1` are emptied, stack `2` is untouched, label `1` reached in state `false`.
#guard out.1.l = some 1
#guard out.1.var = false
#guard (List.finRange 3).map out.1.stk = [[], [], [5, 6]]
-- Within `m + 1 = 4` steps (the longest cleaned stack has 3 symbols).
#guard out.2 ≤ 4
-- Nothing to clean: one round.
#guard (runF 10 (⟨some 0, false, fun _ => []⟩, 0)).2 = 1

end MetaMathlibExt.TM2Program.CleanupTests
