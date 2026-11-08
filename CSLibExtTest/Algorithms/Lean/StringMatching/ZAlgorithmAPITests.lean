/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.ZAlgorithm

set_option autoImplicit false

universe u

open Cslib.Algorithms.Lean.StringMatching

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.StringMatching.extendPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.StringMatching.zStep

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.StringMatching.zScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.StringMatching.computeZ.zScan

example {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Nat) :
    q ≤ (computeZ input).ret[i.val] ↔ q ≤ n - i.val ∧
      input.toList.take q = (input.toList.drop i.val).take q :=
  computeZ_prefix_iff input i q

example {α : Type (u + 1)} [BEq α] {n : Nat} (input : Vector α n) (i : Fin n) :
    (computeZ input).ret[i.val] ≤ n - i.val := computeZ_getElem_le input i

example {α : Type u} [BEq α] {n : Nat} (input : Vector α n) (hn : 0 < n) :
    (computeZ input).ret[0] = n := computeZ_zero input hn

example {α : Type u} [BEq α] {n : Nat} (input : Vector α n) :
    (computeZ input).time ≤ 3 * (n - 1) := computeZ_time_le input

example {α : Type u} [BEq α] {n : Nat} (input : Vector α n) :
    n - 1 ≤ (computeZ input).time := computeZ_time_ge input

example {α : Type u} [BEq α] [LawfulBEq α] (a : α) (n : Nat) :
    (computeZ (Vector.replicate n a)).ret = Vector.ofFn (fun i : Fin n => n - i.val) :=
  computeZ_replicate a n

example {α : Type u} [BEq α] [LawfulBEq α] (a : α) (n : Nat) :
    (computeZ (Vector.replicate n a)).time = 2 * (n - 1) := computeZ_replicate_time a n

example {α : Type u} [BEq α] [LawfulBEq α] (a b : α) (hab : a ≠ b)
    (n : Nat) (hn : 0 < n) :
    (computeZ ((Vector.replicate n a).push b)).time = 3 * n - 1 :=
  computeZ_replicate_push_time a b hab n hn

example : (computeZ (#v[] : Vector Nat 0)).time = 0 := by
  have h := computeZ_time_le (#v[] : Vector Nat 0)
  omega
