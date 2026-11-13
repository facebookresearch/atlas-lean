/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RAMMachines
public import CSLibExt.Computability.Models.Cost.Basic

/-!
# Canonical RAM instruction costs

One abstract time unit is charged for each in-range instruction dispatch,
including `halt` and self-jumps. An already out-of-range PC costs nothing.
The interpreter is the canonical `ramStep`; `CostM` is CSLib's `TimeM Cost`.
The other cost fields are zero annotations because they are unmodeled, not
claims about physical space or memory. No word-RAM, bit-cost, host-runtime,
or complexity-class claim is made.
-/

@[expose] public section

namespace Cslib.Decidability

open CSLibExt.Cost
open Cslib.Algorithms.Lean (TimeM)

/-- Execute the canonical step, charging its in-range dispatch only. -/
def ramStepCost (prog : List RAMInstr) (s : RAMState) : CostM RAMState := do
  TimeM.tick ⟨if s.pc < prog.length then 1 else 0, 0, 0⟩
  pure (ramStep prog s)

/-- Erasing the annotation gives exactly the canonical step. -/
@[simp] theorem ramStepCost_ret (prog : List RAMInstr) (s : RAMState) :
    (ramStepCost prog s).ret = ramStep prog s := rfl

/-- The annotation counts dispatch, not state change or post-halt padding. -/
@[simp] theorem ramStepCost_time (prog : List RAMInstr) (s : RAMState) :
    (ramStepCost prog s).time =
      ⟨if s.pc < prog.length then 1 else 0, 0, 0⟩ := by
  simp [ramStepCost]

/-- Run at most `budget` canonical dispatch opportunities with annotations. -/
def ramExecNCost (prog : List RAMInstr) : ℕ → RAMState → CostM RAMState
  | 0, s => pure s
  | budget + 1, s => do
      let next ← ramExecNCost prog budget s
      ramStepCost prog next

/-- Universal result erasure, including arbitrary initial states. -/
@[simp] theorem ramExecNCost_ret (prog : List RAMInstr) (budget : ℕ)
    (s : RAMState) : (ramExecNCost prog budget s).ret =
      ramExecN prog budget s := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    simpa [ramExecNCost, ramExecN, Function.iterate_succ_apply'] using
      congrArg (ramStep prog) ih

/-- Exact dispatch sum over canonical prefix states. The other fields are
unmodeled annotations, not physical resource measurements. -/
theorem ramExecNCost_time_eq_sum (prog : List RAMInstr) (budget : ℕ)
    (s : RAMState) : (ramExecNCost prog budget s).time =
      ⟨((List.range budget).map fun k =>
        if (ramExecN prog k s).pc < prog.length then 1 else 0).sum, 0, 0⟩ := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    simp only [ramExecNCost, TimeM.time_bind, ramExecNCost_ret,
      ramStepCost_time, ih, List.range_succ, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    rfl

/-- Every budget costs its minimum with the first halt index. `h = 0`
includes empty programs and arbitrary already-halted initial states. -/
theorem ramExecNCost_time_eq_min (prog : List RAMInstr) (s : RAMState)
    (h : ℕ) (hrun : ∀ k < h, (ramExecN prog k s).pc < prog.length)
    (hhalt : prog.length ≤ (ramExecN prog h s).pc) (budget : ℕ) :
    (ramExecNCost prog budget s).time = ⟨min budget h, 0, 0⟩ := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    simp only [ramExecNCost, TimeM.time_bind, ramExecNCost_ret,
      ramStepCost_time, ih]
    change Cost.mk (min budget h +
      if (ramExecN prog budget s).pc < prog.length then 1 else 0) 0 0 = _
    congr 1
    by_cases hk : budget < h
    · rw [ite_eq_left (hrun budget hk)]
      omega
    · have hstable := ramExecN_eq_of_halted hhalt (by omega : h ≤ budget)
      have hout : ¬ (ramExecN prog budget s).pc < prog.length := by
        rw [hstable]
        omega
      rw [ite_eq_right hout]
      omega

/-- A halted costed run witnesses membership in the existing partial RAM
semantics, without replacing its minimization construction. -/
theorem mem_ramEval_of_cost_halted {prog : List RAMInstr}
    {inputs : List ℕ} {budget y : ℕ}
    (hhalt : prog.length ≤ (ramExecNCost prog budget (ramInit inputs)).ret.pc)
    (hout : (ramExecNCost prog budget (ramInit inputs)).ret.acc = y) :
    y ∈ ramEval prog inputs := by
  apply mem_ramEval_of_halted (t := budget)
  · simpa using hhalt
  · simpa using hout

end Cslib.Decidability
