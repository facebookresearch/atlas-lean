/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.List.TakeDrop

/-!
# MULTIPOP and its aggregate cost

CLRS, fourth edition, Section 16.1 (printed pages 449–450). A list stores the
stack with its top first. The loop removes one element while the stack is
nonempty and the requested count is positive. Integer requests at most zero
leave the stack unchanged.

CSLib's `TimeM` counts one event for each actual POP and one for each PUSH.
Guards, decrements, allocation and copying are not charged. This is the
source's abstract stack-operation cost, not a RAM or native runtime bound.
Successful operation sequences have cost at most twice their length plus
the initial stack size; empty POP returns an error and stops the sequence.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.Stack

/-- CLRS MULTIPOP; charge one unit for each top element actually removed. -/
public def multipop {α : Type u} : List α → Nat → TimeM Nat (List α)
  | stack, 0 => pure stack
  | [], _ + 1 => pure []
  | _ :: tail, k + 1 => do
    TimeM.tick 1
    multipop tail k

/-- The timed loop removes exactly the requested prefix, stopping at empty. -/
public theorem multipop_ret {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).ret = stack.drop k := by
  induction k generalizing stack with
  | zero => simp [multipop]
  | succ k ih =>
    cases stack with
    | nil => simp [multipop]
    | cons x xs => simp [multipop, ih]

/-- The actual loop costs one unit per available element in the requested prefix. -/
public theorem multipop_time {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).time = min stack.length k := by
  induction k generalizing stack with
  | zero => simp [multipop]
  | succ k ih =>
    cases stack with
    | nil => simp [multipop]
    | cons x xs =>
      simp [multipop, ih]
      omega

/-- Each actual POP consumes one element, including early exhaustion. -/
private theorem multipop_balance {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).time + (multipop stack k).ret.length = stack.length := by
  simp only [multipop_time, multipop_ret, List.length_drop]
  omega

/-- Integer request interface; nonpositive counts perform no POP. -/
public def multipopSigned {α : Type u} (stack : List α) (k : Int) : TimeM Nat (List α) :=
  multipop stack k.toNat

/-- The source's positive-count guard makes nonpositive requests a complete no-op. -/
public theorem multipopSigned_of_nonpos {α : Type u} (stack : List α) (k : Int) (hk : k ≤ 0) :
    multipopSigned stack k = pure stack := by
  have hz : k.toNat = 0 := by omega
  simp [multipopSigned, hz, multipop]

/-- Stack operations used in CLRS's aggregate-analysis sequence. -/
public inductive Operation (α : Type u) where
  | push (value : α)
  | pop
  | multipop (count : Int)
deriving Repr

/-- Execute the actual sequence, stopping with an error on an empty POP. -/
public def execute {α : Type u} : List α → List (Operation α) → TimeM Nat (Option (List α))
  | stack, [] => pure (some stack)
  | stack, .push value :: ops => do
    TimeM.tick 1
    execute (value :: stack) ops
  | [], .pop :: _ => pure none
  | _ :: tail, .pop :: ops => do
    TimeM.tick 1
    execute tail ops
  | stack, .multipop count :: ops => do
    let next ← multipopSigned stack count
    execute next ops

/-- Actual successful cost and remaining size account for every pushed element. -/
public theorem execute_balance {α : Type u} (stack : List α) (ops : List (Operation α))
    (final : List α) (h : (execute stack ops).ret = some final) :
    (execute stack ops).time + final.length = stack.length +
      2 * ops.countP (fun op => match op with | .push _ => true | _ => false) := by
  induction ops generalizing stack with
  | nil => cases h; simp [execute]
  | cons op ops ih =>
    cases op with
    | push value =>
      have hi := ih (value :: stack) h
      simp [execute] at hi ⊢
      omega
    | pop =>
      cases stack with
      | nil => simp [execute] at h
      | cons value tail =>
        have hi := ih tail h
        simp [execute] at hi ⊢
        omega
    | multipop count =>
      have hi := ih (multipopSigned stack count).ret h
      have hb := multipop_balance stack count.toNat
      simp [execute] at hi ⊢
      change (multipopSigned stack count).time +
        (multipopSigned stack count).ret.length = stack.length at hb
      omega

/-- Every successful sequence costs at most two events per operation plus initial size. -/
public theorem execute_time_le {α : Type u} (stack : List α) (ops : List (Operation α))
    (final : List α) (h : (execute stack ops).ret = some final) :
    (execute stack ops).time ≤ stack.length + 2 * ops.length := by
  have hb := execute_balance stack ops final h
  have hc : ops.countP (fun op => match op with | .push _ => true | _ => false) ≤
      ops.length := List.countP_le_length
  calc
    (execute stack ops).time ≤ (execute stack ops).time + final.length := Nat.le_add_right _ _
    _ = stack.length +
        2 * ops.countP (fun op => match op with | .push _ => true | _ => false) := hb
    _ ≤ stack.length + 2 * ops.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hc) stack.length

end Cslib.Algorithms.Lean.Stack
