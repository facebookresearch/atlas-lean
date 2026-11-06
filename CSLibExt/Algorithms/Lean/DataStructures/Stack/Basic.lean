/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Standalone stack operations

The existing top-first `List` carrier is unchanged. A successful PUSH, POP,
or TOP counts one selected stack event; underflow returns `none` and costs
zero. Guards, allocation, copying and machine instructions are not charged.
The existing MULTIPOP and sequence cost convention is unchanged.

This first additive increment was authored by Codex at Adam Kiezun's
selection.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean.Stack

/-- **Stack push.** Stacks over a type $\alpha$ are lists of elements of $\alpha$, with the first
element as the top. Pushing $v \in \alpha$ onto a stack $s$ returns the stack with top $v$
followed by the elements of $s$, at cost $1$ (one successful push event). -/
def push {α : Type u} (stack : List α) (value : α) : TimeM Nat (List α) := do
  TimeM.tick 1
  pure (value :: stack)

/-- **Stack pop.** Stacks over a type $\alpha$ are lists of elements of $\alpha$, with the first
element as the top. Popping the empty stack returns underflow (no value) at cost $0$. Popping a
stack with top $v$ and remaining stack $t$ returns the pair $(v, t)$ at cost $1$ (one successful
pop event). -/
def pop {α : Type u} : List α → TimeM Nat (Option (α × List α))
  | [] => pure none
  | value :: tail => do
    TimeM.tick 1
    pure (some (value, tail))

/-- **Stack top.** Stacks over a type $\alpha$ are lists of elements of $\alpha$, with the first
element as the top. Reading the top of the empty stack returns underflow (no value) at cost $0$.
Reading the top of a stack with top $v$ returns $v$ at cost $1$ (one successful top event); the
stack itself is not returned or changed. -/
def top {α : Type u} : List α → TimeM Nat (Option α)
  | [] => pure none
  | value :: _ => do
    TimeM.tick 1
    pure (some value)

/-- **Result and cost of stack pop.** Let $s$ be a stack over a type $\alpha$ (a list of elements
of $\alpha$ whose first element is the top). If $s$ is empty, popping $s$ returns underflow (no
value) at cost $0$. If $s$ has top $h$ and remaining stack $t$, popping $s$ returns the pair
$(h, t)$ at cost $1$.

This holds for every type $\alpha$; no element of $\alpha$ is assumed to exist. -/
theorem pop_eq {α : Type u} (stack : List α) :
    pop stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: tail => ⟨some (head, tail), 1⟩) := by
  cases stack <;> rfl

/-- **Result and cost of reading the stack top.** Let $s$ be a stack over a type $\alpha$ (a list
of elements of $\alpha$ whose first element is the top). If $s$ is empty, reading the top of $s$
returns underflow (no value) at cost $0$. If $s$ has top $h$, reading the top of $s$ returns $h$
at cost $1$.

This holds for every type $\alpha$; no element of $\alpha$ is assumed to exist. -/
theorem top_eq {α : Type u} (stack : List α) :
    top stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: _ => ⟨some head, 1⟩) := by
  cases stack <;> rfl

/-- **Result and cost of the stack operations.** Let $\alpha$ be a type, let $s$ be a stack over
$\alpha$ (a list of elements of $\alpha$ whose first element is the top) and let $v \in \alpha$.
Pushing $v$ onto $s$ returns the stack with top $v$ followed by the elements of $s$, at cost $1$.
Popping $s$ returns underflow (no value) at cost $0$ if $s$ is empty, and returns the pair
$(h, t)$ at cost $1$ if $s$ has top $h$ and remaining stack $t$. Reading the top of $s$ returns
underflow (no value) at cost $0$ if $s$ is empty, and returns $h$ at cost $1$ if $s$ has top $h$. -/
theorem operations_spec {α : Type u} (stack : List α) (value : α) :
    push stack value = ⟨value :: stack, 1⟩ ∧
    pop stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: tail => ⟨some (head, tail), 1⟩) ∧
    top stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: _ => ⟨some head, 1⟩) := by
  cases stack with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons head tail => exact ⟨rfl, rfl, rfl⟩

end Cslib.Algorithms.Lean.Stack
