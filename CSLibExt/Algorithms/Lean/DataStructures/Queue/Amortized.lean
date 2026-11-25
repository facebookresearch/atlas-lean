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

/-- **Potential of a two-list queue.** For a queue stored as an enqueue list and a dequeue list, the
potential is the length of the enqueue list: the number of elements that will be reversed when
they are moved to the dequeue list. -/
def potential (q : Std.Queue α) : Nat :=
  q.eList.length

/-- **Modeled cost of a dequeue.** For a queue stored as an enqueue list and a dequeue list, the
modeled cost of dequeueing is $1$ when the dequeue list is nonempty, and $m + 1$ when the dequeue
list is empty, where $m$ is the length of the enqueue list (the number of elements reversed when
they are moved to the dequeue list). -/
def dequeueCost (q : Std.Queue α) : Nat :=
  if q.dList.isEmpty then q.eList.length + 1 else 1

/-- **Timed enqueue.** Enqueueing a value $v$ onto a two-list queue $q$ returns the queue
obtained from $q$ by adding $v$ at the back, that is, by prepending $v$ to the enqueue list,
together with a recorded cost of $1$. -/
def enqueue (q : Std.Queue α) (value : α) : TimeM Nat (Std.Queue α) :=
  ⟨q.enqueue value, 1⟩

@[simp]
theorem enqueue_ret (q : Std.Queue α) (value : α) :
    (enqueue q value).ret = q.enqueue value := rfl

@[simp]
theorem enqueue_time (q : Std.Queue α) (value : α) :
    (enqueue q value).time = 1 := rfl

/-- **Amortized cost of enqueueing.** For every two-list queue $q$ and every value $v$, the modeled
cost of enqueueing $v$ onto $q$ plus the potential of the resulting queue equals the potential of
$q$ plus $2$. -/
theorem enqueue_amortized (q : Std.Queue α) (value : α) :
    (enqueue q value).time + potential (enqueue q value).ret = potential q + 2 := by
  simp [potential, Std.Queue.enqueue]
  omega

/-- **Timed dequeue.** Dequeueing from a two-list queue $q$ returns the next element in first-in,
first-out order together with the remaining queue, or returns no element together with $q$ itself
when $q$ is empty. In both cases the recorded cost is the modeled dequeue cost of $q$. -/
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

/-- **Amortized cost of dequeueing.** For every two-list queue $q$, the modeled cost of dequeueing
from $q$ plus the potential of the resulting queue equals the potential of $q$ plus $1$. This
includes the case where $q$ is empty. -/
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

/-- **Queue operation.** A queue operation over a type $\alpha$ is either a request to enqueue a
value $v \in \alpha$ or a request to dequeue. Sequences of such operations are used to state
aggregate cost bounds. -/
inductive Operation (α : Type u) where
  | enqueue (value : α)
  | dequeue

/-- **Amortized charge of a queue operation.** The potential-method charge of a queue operation is
$2$ for an enqueue and $1$ for a dequeue. -/
def Operation.charge : Operation α → Nat
  | .enqueue _ => 2
  | .dequeue => 1

/-- **One step of a queue operation.** For a queue $q$, an enqueue operation with value $v$
performs the costed enqueue of $v$ onto $q$. A dequeue operation performs the costed dequeue
of $q$ and keeps the remaining queue and the cost, discarding the removed value; on an empty
queue the remaining queue is $q$ itself. -/
def step (q : Std.Queue α) : Operation α → TimeM Nat (Std.Queue α)
  | .enqueue value => enqueue q value
  | .dequeue =>
      let result := dequeue q
      ⟨result.ret.2, result.time⟩

/-- **Amortized cost of one queue operation.** For every queue $q$ and every queue operation
$o$, the modeled cost of performing $o$ on $q$ plus the potential of the resulting queue equals
the potential of $q$ plus the charge of $o$. -/
theorem step_amortized (q : Std.Queue α) (op : Operation α) :
    (step q op).time + potential (step q op).ret = potential q + op.charge := by
  cases op with
  | enqueue value => simpa [step, Operation.charge] using enqueue_amortized q value
  | dequeue => simpa [step, Operation.charge] using dequeue_amortized q

/-- **Running a sequence of queue operations.** Running a list of queue operations from a
queue $q$ performs the operations one step at a time from left to right, starting at $q$.
The result is the final queue, and the cost is the sum of the costs of the individual
steps; running the empty list returns $q$ at cost $0$. -/
def run : List (Operation α) → Std.Queue α → TimeM Nat (Std.Queue α)
  | [], q => ⟨q, 0⟩
  | op :: ops, q =>
      let first := step q op
      let rest := run ops first.ret
      ⟨rest.ret, first.time + rest.time⟩

/-- **Total charge of a sequence of queue operations.** For a list of queue operations, the
total charge is the sum of the amortized charges of its operations, where an enqueue is charged
$2$ and a dequeue is charged $1$. -/
def totalCharge (ops : List (Operation α)) : Nat :=
  (ops.map Operation.charge).sum

/-- **Amortized cost of a sequence of queue operations.** For every list of queue operations and
every two-list queue $q$, the modeled cost of running the operations from left to right starting
at $q$, plus the potential of the final queue, equals the potential of $q$ plus the total charge
of the operations. -/
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

/-- **Linear bound on the cost of queue operations.** For every list of $n$ queue operations and
every two-list queue $q$, the modeled cost of running the operations from left to right starting
at $q$ is at most the potential of $q$ plus $2n$. -/
theorem run_time_le_potential_add_twice_length
    (ops : List (Operation α)) (q : Std.Queue α) :
    (run ops q).time ≤ potential q + 2 * ops.length := by
  have hamortized := run_amortized ops q
  have hcharge := totalCharge_le_twice_length ops
  omega

end Cslib.Algorithms.Lean.Queue.Amortized
