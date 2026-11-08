/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Stack.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.Stack.Multipop

public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.Stack.BasicAPITests

open Cslib.Algorithms.Lean.Stack

theorem push_spec {α : Type u} (stack : List α) (value : α) :
    push stack value = ⟨value :: stack, 1⟩ := (operations_spec stack value).1

theorem pop_spec {α : Type u} (stack : List α) :
    pop stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: tail => ⟨some (head, tail), 1⟩) :=
  pop_eq stack

theorem top_spec {α : Type u} (stack : List α) :
    top stack = (match stack with
      | [] => ⟨none, 0⟩
      | head :: _ => ⟨some head, 1⟩) :=
  top_eq stack

theorem pop_empty {α : Type u} : pop ([] : List α) = ⟨none, 0⟩ :=
  pop_eq []

theorem top_empty {α : Type u} : top ([] : List α) = ⟨none, 0⟩ :=
  top_eq []

theorem pop_empty_type : pop ([] : List Empty) = ⟨none, 0⟩ := pop_eq []

theorem top_empty_type : top ([] : List Empty) = ⟨none, 0⟩ := top_eq []

theorem pop_cons {α : Type u} (stack : List α) (value : α) :
    pop (value :: stack) = ⟨some (value, stack), 1⟩ :=
  (operations_spec (value :: stack) value).2.1

theorem top_cons {α : Type u} (stack : List α) (value : α) :
    top (value :: stack) = ⟨some value, 1⟩ :=
  (operations_spec (value :: stack) value).2.2

theorem sequence_push_spec {α : Type u} (stack : List α) (value : α)
    (ops : List (Operation α)) :
    execute stack (.push value :: ops) = (do
      let next ← push stack value
      execute next ops) :=
  execute_push_eq_bind_push stack value ops

theorem sequence_pop_spec {α : Type u} (stack : List α) (ops : List (Operation α)) :
    execute stack (.pop :: ops) = (do
      let removed ← pop stack
      match removed with
      | none => pure none
      | some (_, next) => execute next ops) :=
  execute_pop_eq_bind_pop stack ops

end Cslib.Algorithms.Lean.Stack.BasicAPITests
