/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Models.Cost.RAM

/-!
# Countdown as a consumer of canonical RAM instruction costs

The initial load takes one instruction. Each positive iteration takes three
(`jz`, `sub`, `jump`), then the zero case takes `jz` and `halt`. Thus the first
out-of-range PC occurs at `3 * n + 3`, not when the accumulator first is zero.
Costs are abstract dispatch counts; space and memory remain unmodeled.
-/

@[expose] public section

namespace Cslib.Decidability

/-- Load register zero, count down to zero, then dispatch `halt`. -/
def ramCountdown : List RAMInstr :=
  [.load (.dir 0), .jz 4, .sub (.imm 1), .jump 1, .halt]

private theorem countdown_three (n : ℕ) (regs : ℕ → ℕ) :
    ramExecN ramCountdown 3 ⟨1, n + 1, regs⟩ = ⟨1, n, regs⟩ := rfl

private theorem countdown_loop_halt (n : ℕ) (regs : ℕ → ℕ) :
    ramExecN ramCountdown (3 * n + 2) ⟨1, n, regs⟩ =
      ⟨5, 0, regs⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) + 2 = (3 * n + 2) + 3 by omega]
    change (ramStep ramCountdown)^[(3 * n + 2) + 3] _ = _
    rw [Function.iterate_add_apply]
    change ramExecN ramCountdown (3 * n + 2)
      (ramExecN ramCountdown 3 ⟨1, n + 1, regs⟩) = _
    rw [countdown_three]
    exact ih

private theorem countdown_three_active (n : ℕ) (regs : ℕ → ℕ)
    (k : ℕ) (hk : k < 3) :
    (ramExecN ramCountdown k ⟨1, n + 1, regs⟩).pc < 5 := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact (by decide : 1 < 5)
  · exact (by decide : 2 < 5)
  · exact (by decide : 3 < 5)

private theorem countdown_loop_active (n : ℕ) (regs : ℕ → ℕ) :
    ∀ k < 3 * n + 2, (ramExecN ramCountdown k ⟨1, n, regs⟩).pc < 5 := by
  induction n with
  | zero =>
    intro k hk
    have cases : k = 0 ∨ k = 1 := by omega
    rcases cases with rfl | rfl
    · exact (by decide : 1 < 5)
    · exact (by decide : 4 < 5)
  | succ n ih =>
    intro k hk
    by_cases hsmall : k < 3
    · exact countdown_three_active n regs k hsmall
    · rw [show k = (k - 3) + 3 by omega]
      change ((ramStep ramCountdown)^[(k - 3) + 3] _).pc < 5
      rw [Function.iterate_add_apply]
      change (ramExecN ramCountdown (k - 3)
        (ramExecN ramCountdown 3 ⟨1, n + 1, regs⟩)).pc < 5
      rw [countdown_three]
      exact ih (k - 3) (by omega)

/-- The countdown run has dispatched `halt` and returns zero at `3*n+3`. -/
theorem ramCountdown_halted (n : ℕ) :
    ramExecN ramCountdown (3 * n + 3) (ramInit [n]) =
      { ramInit [n] with pc := ramCountdown.length, acc := 0 } := by
  rw [show 3 * n + 3 = (3 * n + 2) + 1 by omega]
  change ramExecN ramCountdown (3 * n + 2)
    ⟨1, n, (ramInit [n]).regs⟩ = _
  exact countdown_loop_halt n (ramInit [n]).regs

/-- Every earlier PC is in range: the halt above is the first halt. -/
theorem ramCountdown_before_halt (n k : ℕ) (hk : k < 3 * n + 3) :
    (ramExecN ramCountdown k (ramInit [n])).pc < ramCountdown.length := by
  cases k with
  | zero => simp [ramExecN, ramInit, ramCountdown]
  | succ k =>
    change (ramExecN ramCountdown k ⟨1, n, (ramInit [n]).regs⟩).pc < 5
    exact countdown_loop_active n (ramInit [n]).regs k (by omega)

/-- Exact instruction cost for every input and budget, with no padding. -/
theorem ramCountdown_cost (n budget : ℕ) :
    (ramExecNCost ramCountdown budget (ramInit [n])).time =
      ⟨min budget (3 * n + 3), 0, 0⟩ := by
  apply ramExecNCost_time_eq_min
  · exact ramCountdown_before_halt n
  · rw [ramCountdown_halted]

/-- Countdown computes zero in the canonical partial RAM semantics. -/
theorem zero_mem_ramCountdown (n : ℕ) : 0 ∈ ramEval ramCountdown [n] := by
  apply mem_ramEval_of_cost_halted (budget := 3 * n + 3)
  · simp [ramCountdown_halted]
  · simp [ramCountdown_halted]

end Cslib.Decidability
