/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Init.Data.Queue

import all Init.Data.Queue

/-!
# Amortized cost of `Std.Queue`

This file equips Lean's two-list queue with a `TimeM Nat` cost model. Enqueueing costs one unit.
Dequeueing costs one unit plus the length of the enqueue list exactly when that list is reversed.
The potential is the enqueue-list length, making the amortized charges two for enqueue and one for
dequeue.

The costs describe this explicit model, not compiler or wall-clock time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Queue.Amortized

universe u

variable {α : Type u}

/-- The number of queued elements waiting in the list that the next transfer reverses. -/
def potential (q : Std.Queue α) : Nat :=
  q.eList.length

/-- The modeled cost of dequeueing: one unit plus the number of elements reversed. -/
def dequeueCost (q : Std.Queue α) : Nat :=
  if q.dList.isEmpty then q.eList.length + 1 else 1

/-- Enqueues one value and charges one unit. -/
def enqueue (q : Std.Queue α) (value : α) : TimeM Nat (Std.Queue α) :=
  ⟨q.enqueue value, 1⟩

@[simp]
theorem enqueue_ret (q : Std.Queue α) (value : α) :
    (enqueue q value).ret = q.enqueue value := rfl

@[simp]
theorem enqueue_time (q : Std.Queue α) (value : α) :
    (enqueue q value).time = 1 := rfl

/-- Enqueueing has amortized charge two. -/
theorem enqueue_amortized (q : Std.Queue α) (value : α) :
    (enqueue q value).time + potential (enqueue q value).ret = potential q + 2 := by
  simp [potential, Std.Queue.enqueue]
  omega

/-- Dequeues one value, retaining the input queue when it is empty. -/
def dequeue (q : Std.Queue α) : TimeM Nat (Option α × Std.Queue α) :=
  ⟨match q.dequeue? with
    | none => (none, q)
    | some (value, rest) => (some value, rest),
   dequeueCost q⟩

@[simp]
theorem dequeue_ret (q : Std.Queue α) :
    (dequeue q).ret =
      match q.dequeue? with
      | none => (none, q)
      | some (value, rest) => (some value, rest) := rfl

@[simp]
theorem dequeue_time (q : Std.Queue α) :
    (dequeue q).time = dequeueCost q := rfl

/-- Dequeueing has amortized charge one, including on an empty queue. -/
theorem dequeue_amortized (q : Std.Queue α) :
    (dequeue q).time + potential (dequeue q).ret.2 = potential q + 1 := by
  cases q with
  | mk eList dList =>
      cases dList with
      | cons head tail =>
          simp [dequeue, dequeueCost, potential, Std.Queue.dequeue?]
          omega
      | nil =>
          cases h : eList.reverse with
          | nil =>
              have he : eList = [] := by
                simpa using congrArg List.reverse h
              subst eList
              simp [dequeue, dequeueCost, potential, Std.Queue.dequeue?]
          | cons head tail =>
              simp [dequeue, dequeueCost, potential, Std.Queue.dequeue?, h]

/-- An enqueue or dequeue request, used to state aggregate cost bounds. -/
inductive Operation (α : Type u) where
  | enqueue (value : α)
  | dequeue

/-- The potential-method charge assigned to one queue operation. -/
def Operation.charge : Operation α → Nat
  | .enqueue _ => 2
  | .dequeue => 1

/-- Executes one operation and discards the value removed by a dequeue. -/
def step (q : Std.Queue α) : Operation α → TimeM Nat (Std.Queue α)
  | .enqueue value => enqueue q value
  | .dequeue =>
      let result := dequeue q
      ⟨result.ret.2, result.time⟩

/-- Each operation's actual cost plus final potential equals its assigned charge plus initial
potential. -/
theorem step_amortized (q : Std.Queue α) (op : Operation α) :
    (step q op).time + potential (step q op).ret = potential q + op.charge := by
  cases op with
  | enqueue value => simpa [step, Operation.charge] using enqueue_amortized q value
  | dequeue => simpa [step, Operation.charge] using dequeue_amortized q

/-- Executes queue operations from left to right, accumulating modeled cost. -/
def run : List (Operation α) → Std.Queue α → TimeM Nat (Std.Queue α)
  | [], q => ⟨q, 0⟩
  | op :: ops, q =>
      let first := step q op
      let rest := run ops first.ret
      ⟨rest.ret, first.time + rest.time⟩

/-- The sum of the potential-method charges for a sequence of operations. -/
def totalCharge (ops : List (Operation α)) : Nat :=
  (ops.map Operation.charge).sum

/-- Potential changes telescope over a sequence of queue operations. -/
theorem run_amortized (ops : List (Operation α)) (q : Std.Queue α) :
    (run ops q).time + potential (run ops q).ret = potential q + totalCharge ops := by
  induction ops generalizing q with
  | nil => simp [run, totalCharge]
  | cons op ops ih =>
      have hstep := step_amortized q op
      have htail := ih (q := (step q op).ret)
      simp only [totalCharge] at htail
      simp only [run, totalCharge, List.map_cons, List.sum_cons]
      omega

private theorem totalCharge_le_twice_length (ops : List (Operation α)) :
    totalCharge ops ≤ 2 * ops.length := by
  induction ops with
  | nil => simp [totalCharge]
  | cons op ops ih =>
      cases op <;> simp [totalCharge, Operation.charge] at ih ⊢ <;> omega

/-- Any sequence of `n` operations costs at most its initial potential plus `2 * n`. -/
theorem run_time_le_potential_add_twice_length
    (ops : List (Operation α)) (q : Std.Queue α) :
    (run ops q).time ≤ potential q + 2 * ops.length := by
  have hamortized := run_amortized ops q
  have hcharge := totalCharge_le_twice_length ops
  omega

end Cslib.Algorithms.Lean.Queue.Amortized
