/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.Stack.Multipop

open Cslib.Algorithms.Lean.Stack

universe u

example {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).ret = stack.drop k := multipop_ret stack k

example {α : Type u} (stack : List α) (k : Nat) :
    (multipop stack k).time = min stack.length k := multipop_time stack k

example {α : Type u} (stack : List α) (k : Int) (hk : k ≤ 0) :
    multipopSigned stack k = pure stack := multipopSigned_of_nonpos stack k hk

example {α : Type u} (stack : List α) (ops : List (Operation α))
    (final : List α) (h : (execute stack ops).ret = some final) :
    (execute stack ops).time + final.length = stack.length +
      2 * ops.countP (fun op => match op with | .push _ => true | _ => false) :=
  execute_balance stack ops final h

example {α : Type u} (stack : List α) (ops : List (Operation α))
    (final : List α) (h : (execute stack ops).ret = some final) :
    (execute stack ops).time ≤ stack.length + 2 * ops.length :=
  execute_time_le stack ops final h

example {α : Type u} (ops : List (Operation α))
    (final : List α) (h : (execute [] ops).ret = some final) :
    (execute [] ops).time ≤ 2 * ops.length := by
  simpa using execute_time_le [] ops final h
