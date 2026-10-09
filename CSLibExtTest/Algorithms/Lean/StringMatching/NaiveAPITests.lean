/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Naive

@[expose] public section

set_option autoImplicit false

universe u

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.TimeM

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.timedPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.timedScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.naiveMatches.timedPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.naiveMatches.timedScan

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α) (offset : Nat) :
    offset ∈ (naiveMatches pattern text).ret ↔ MatchAt pattern text offset :=
  mem_naiveMatches_iff pattern text offset

example {α : Type (u + 1)} [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).ret.Pairwise (· < ·) := naiveMatches_pairwise pattern text

example {α : Type u} [BEq α] (text : List α) :
    naiveMatches [] text = ⟨List.range (text.length + 1), 0⟩ := naiveMatches_nil_pattern text

example : (naiveMatches ([0, 0] : List Nat) [0, 0, 0]).ret = [0, 1] := by
  rw [naiveMatches_ret]
  decide

example : (naiveMatches ([0, 0, 1] : List Nat) [0, 0, 0, 0]).time = 6 := by
  rw [naiveMatches_time_eq]
  decide

example {α : Type u} [BEq α] [ReflBEq α] (x : α) (m n : Nat) (hlen : m ≤ n) :
    (naiveMatches (List.replicate m x) (List.replicate n x)).time = (n - m + 1) * m :=
  naiveMatches_time_replicate x m n hlen
