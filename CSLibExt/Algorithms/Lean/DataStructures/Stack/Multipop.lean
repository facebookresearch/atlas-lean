/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Stack.Basic
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

/-- **MULTIPOP.** For a stack $S$, stored as a list with its top first, and a natural number $k$,
MULTIPOP of $S$ with count $k$ repeatedly removes the top element while the stack is nonempty and
fewer than $k$ elements have been removed, and returns the remaining stack. Each removed element
costs one unit, and nothing else is charged.

This is MULTIPOP from CLRS, fourth edition, Section 16.1. -/
public def multipop {α : Type u} : List α → Nat → TimeM Nat (List α)
  | stack, 0 => pure stack
  | [], _ + 1 => pure []
  | _ :: tail, k + 1 => do
    TimeM.tick 1
    multipop tail k

/-- **Result of MULTIPOP.** For every stack $S$, stored as a list with its top first, and every
natural number $k$, the stack returned by MULTIPOP of $S$ with count $k$ is $S$ with its top $k$
elements removed, or the empty stack if $S$ has fewer than $k$ elements. -/
public theorem multipop_ret {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).ret = stack.drop k := by
  induction k generalizing stack with
  | zero => simp [multipop]
  | succ k ih =>
    cases stack with
    | nil => simp [multipop]
    | cons x xs => simp [multipop, ih]

/-- **Cost of MULTIPOP.** For every stack $S$ and every natural number $k$, the cost of MULTIPOP
of $S$ with count $k$ is $\min(|S|, k)$, where $|S|$ is the number of elements of $S$. -/
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

/-- **MULTIPOP with an integer count.** For a stack $S$ and an integer $k$, MULTIPOP with integer
count $k$ is MULTIPOP of $S$ with the natural count $\max(k, 0)$, with the same result and cost.
In particular, a count $k \le 0$ removes nothing. -/
public def multipopSigned {α : Type u} (stack : List α) (k : Int) : TimeM Nat (List α) :=
  multipop stack k.toNat

/-- **MULTIPOP with a nonpositive count does nothing.** For every stack $S$ and every integer
$k \le 0$, MULTIPOP with integer count $k$ applied to $S$ returns $S$ at cost $0$. -/
public theorem multipopSigned_of_nonpos {α : Type u} (stack : List α) (k : Int) (hk : k ≤ 0) :
    multipopSigned stack k = pure stack := by
  have hz : k.toNat = 0 := by omega
  simp [multipopSigned, hz, multipop]

/-- **Stack operations for the MULTIPOP aggregate analysis.** For a type $\alpha$ of stack
entries, a stack operation is one of the following: $\mathrm{PUSH}(x)$ for an element
$x \in \alpha$, $\mathrm{POP}$, or $\mathrm{MULTIPOP}(k)$ for an integer count $k$.

These are the operations whose sequences CLRS analyse in Section 16.1. -/
public inductive Operation (α : Type u) where
  | push (value : α)
  | pop
  | multipop (count : Int)
deriving Repr

/-- **Running a sequence of stack operations.** Given a stack $S$ and a finite sequence of
operations, each a PUSH of a value, a POP or a MULTIPOP with an integer count, the operations are
applied to $S$ in order. PUSH of $x$ puts $x$ on top at cost $1$; POP removes the top element at
cost $1$; MULTIPOP with count $k$ is MULTIPOP with an integer count, costing one unit per element
removed. If a POP meets an empty stack, the run stops and reports an error, that POP is not
charged, and the cost is that of the operations before it. Otherwise the run returns the final
stack, and its cost is the sum of the costs of all operations. -/
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

/-- **Running a PUSH agrees with the standalone PUSH.** For every stack $S$, every value $x$ and
every finite sequence $\sigma$ of stack operations, running PUSH $x$ followed by $\sigma$ on $S$
has the same result and cost as first performing the standalone PUSH of $x$ on $S$ and then
running $\sigma$ on the resulting stack, the two costs being added. -/
public theorem execute_push_eq_bind_push {α : Type u} (stack : List α) (value : α)
    (ops : List (Operation α)) :
    execute stack (.push value :: ops) = (do
      let next ← push stack value
      execute next ops) := by
  rfl

/-- **Running a POP agrees with the standalone POP.** For every stack $S$ and every finite
sequence $\sigma$ of stack operations, running POP followed by $\sigma$ on $S$ has the same result
and cost as first performing the standalone POP on $S$ and then, if it reports underflow,
stopping with an error at no further cost, or, if it removes the top element and leaves the stack
$S'$, running $\sigma$ on $S'$, the two costs being added. -/
public theorem execute_pop_eq_bind_pop {α : Type u} (stack : List α)
    (ops : List (Operation α)) :
    execute stack (.pop :: ops) = (do
      let removed ← pop stack
      match removed with
      | none => pure none
      | some (_, next) => execute next ops) := by
  cases stack <;> rfl

/-- **Cost balance for stack operation sequences.** For every stack $S$ and every finite sequence
$\sigma$ of stack operations, if running $\sigma$ on $S$ succeeds with final stack $F$, then the
cost of the run plus the number of elements of $F$ equals the number of elements of $S$ plus
twice the number of PUSH operations in $\sigma$. -/
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

/-- **Aggregate cost of stack operation sequences.** For every stack $S$ and every sequence of
$n$ stack operations (PUSH, POP and MULTIPOP), if running the sequence on $S$ succeeds, that is,
no POP meets an empty stack, then its cost is at most $|S| + 2n$, where $|S|$ is the number of
elements of $S$. -/
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
