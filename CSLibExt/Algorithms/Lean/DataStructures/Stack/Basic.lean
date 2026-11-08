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

/-- Add a new top element, charging one successful PUSH event. -/
def push {α : Type u} (stack : List α) (value : α) : TimeM Nat (List α) := do
  TimeM.tick 1
  pure (value :: stack)

/-- Return the removed element and remaining stack, or explicit underflow. -/
def pop {α : Type u} : List α → TimeM Nat (Option (α × List α))
  | [] => pure none
  | value :: tail => do
    TimeM.tick 1
    pure (some (value, tail))

/-- Observe the top without changing the input stack, or explicit underflow. -/
def top {α : Type u} : List α → TimeM Nat (Option α)
  | [] => pure none
  | value :: _ => do
    TimeM.tick 1
    pure (some value)

/-- POP refinement and cost do not require an inhabitant of the element type. -/
theorem pop_eq {α : Type u} (stack : List α) :
    pop stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: tail => ⟨some (head, tail), 1⟩) := by
  cases stack <;> rfl

/-- TOP refinement and cost do not require an inhabitant of the element type. -/
theorem top_eq {α : Type u} (stack : List α) :
    top stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: _ => ⟨some head, 1⟩) := by
  cases stack <;> rfl

/-- Exact list refinement and selected-event costs, including underflow. -/
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
