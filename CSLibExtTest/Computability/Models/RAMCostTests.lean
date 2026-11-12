/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Models.Cost.RAMCountdown
meta import CSLibExt.Computability.Models.Cost.RAMCountdown

/-! Executable boundaries for canonical RAM instruction accounting. -/

open Cslib.Decidability CSLibExt.Cost

private def input : RAMState := ramInit [2, 7, 11, 13, 17, 19]

private def snapshot (prog : List RAMInstr) (budget : ℕ)
    (s : RAMState := input) : ℕ × ℕ × Cost × List ℕ :=
  let result := ramExecNCost prog budget s
  (result.ret.pc, result.ret.acc, result.time,
    (List.range 6).map result.ret.regs)

#guard (ramStepCost [.halt] input).time = ⟨1, 0, 0⟩
#guard (ramStepCost [] input).time = ⟨0, 0, 0⟩
#guard snapshot [] 9 = (0, 0, ⟨0, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.halt] 0 = (0, 0, ⟨0, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.halt] 1 = (1, 0, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.halt] 9 = (1, 0, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.halt] 9 { input with pc := 9, acc := 23 } =
  (9, 23, ⟨0, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.jump 0] 17 =
  (0, 0, ⟨17, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.jump 9] 17 =
  (9, 0, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.load (.imm 4)] 7 =
  (1, 4, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.load (.dir 0)] 1 =
  (1, 2, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.load (.ind 0)] 1 =
  (1, 11, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.load (.imm 31), .store (.dir 0)] 2 =
  (2, 31, ⟨2, 0, 0⟩, [31, 7, 11, 13, 17, 19])
#guard snapshot [.load (.imm 31), .store (.ind 0)] 2 =
  (2, 31, ⟨2, 0, 0⟩, [2, 7, 31, 13, 17, 19])
#guard snapshot [.load (.imm 1), .add (.dir 1), .add (.ind 0)] 3 =
  (3, 19, ⟨3, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.load (.imm 2), .sub (.imm 5)] 2 =
  (2, 0, ⟨2, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.jz 3] 1 =
  (3, 0, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot [.jz 3] 1 { input with acc := 8 } =
  (1, 8, ⟨1, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot ramCountdown 8 =
  (4, 0, ⟨8, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot ramCountdown 9 =
  (5, 0, ⟨9, 0, 0⟩, [2, 7, 11, 13, 17, 19])
#guard snapshot ramCountdown 12 =
  (5, 0, ⟨9, 0, 0⟩, [2, 7, 11, 13, 17, 19])

-- Kernel-checked consumers, including first halt at zero.
example (budget : ℕ) (s : RAMState) :
    (ramExecNCost [] budget s).time = ⟨0, 0, 0⟩ := by
  simpa using ramExecNCost_time_eq_min [] s 0 (by simp) (by simp) budget

example (n budget : ℕ) :
    (ramExecNCost ramCountdown budget (ramInit [n])).time.time =
      min budget (3 * n + 3) := by
  rw [ramCountdown_cost]

example (n : ℕ) : 0 ∈ ramEval ramCountdown [n] := zero_mem_ramCountdown n

/-- Closed-form oracle, independent of both interpreters and cost recursion. -/
private def expectedCountdown (n budget : ℕ) : ℕ × ℕ × Cost × List ℕ :=
  let state := if budget = 0 then (0, 0)
    else if budget ≤ 3 * n + 1 then
      let q := (budget - 1) / 3
      let r := (budget - 1) % 3
      if r = 0 then (1, n - q)
      else if r = 1 then (2, n - q)
      else (3, n - q - 1)
    else if budget = 3 * n + 2 then (4, 0)
    else (5, 0)
  (state.1, state.2, ⟨min budget (3 * n + 3), 0, 0⟩, [n, 0, 0, 0, 0, 0])

#eval show IO Unit from do
  let mut checked := 0
  for n in List.range 65 do
    for budget in List.range (3 * n + 8) do
      let actual := snapshot ramCountdown budget (ramInit [n])
      let expected := expectedCountdown n budget
      unless actual == expected do
        throw <| IO.userError
          (s!"COUNTDOWN_MISMATCH n={n} budget={budget}: " ++
            s!"{reprStr actual} != {reprStr expected}")
      checked := checked + 1
  unless checked = 6760 do
    throw <| IO.userError s!"Wrong coverage: {checked}"
  IO.println s!"RAM: 21 boundary guards and {checked} countdown cases passed"
