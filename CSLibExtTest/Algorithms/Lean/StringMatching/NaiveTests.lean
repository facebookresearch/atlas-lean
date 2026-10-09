/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Basic
public meta import CSLibExt.Algorithms.Lean.StringMatching.Naive

@[expose] public section

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.TimeM

universe u

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check timedPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check timedScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check naiveMatches.timedPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check naiveMatches.timedScan

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α) (offset : Nat) :
    offset ∈ (naiveMatches pattern text).ret ↔ MatchAt pattern text offset :=
  mem_naiveMatches_iff pattern text offset

example {α : Type (u + 1)} [BEq α] [LawfulBEq α] (pattern text : List α) (offset : Nat) :
    offset ∈ (naiveMatches pattern text).ret ↔ MatchAt pattern text offset :=
  mem_naiveMatches_iff pattern text offset

example {α : Type u} [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).ret.Pairwise (· < ·) := naiveMatches_pairwise pattern text

example {α : Type u} [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).time ≤
      if pattern.length ≤ text.length then (text.length - pattern.length + 1) * pattern.length
      else 0 := naiveMatches_time_le pattern text

example : (naiveMatches ([0, 0] : List Nat) [0, 0, 0]).ret = [0, 1] := by
  rw [naiveMatches_ret]
  decide

example : (naiveMatches ([0, 0] : List Nat) [0, 0, 0]).time = 4 := by
  rw [naiveMatches_time_eq]
  decide

example : (naiveMatches ([0, 0, 1] : List Nat) [0, 0, 0, 0]).time = 6 := by
  rw [naiveMatches_time_eq]
  decide

example : naiveMatches ([] : List Nat) [0, 1] = ⟨[0, 1, 2], 0⟩ := by
  rw [naiveMatches_nil_pattern]
  rfl

example : naiveMatches ([0, 0] : List Nat) [0] = pure [] :=
  naiveMatches_of_length_lt _ _ (by decide)

example (m n : Nat) (hlen : m ≤ n) :
    (naiveMatches (List.replicate m 0) (List.replicate n 0)).ret = List.range (n - m + 1) :=
  naiveMatches_ret_replicate 0 m n hlen

example (m n : Nat) (hlen : m ≤ n) :
    (naiveMatches (List.replicate m 0) (List.replicate n 0)).time = (n - m + 1) * m :=
  naiveMatches_time_replicate 0 m n hlen

private inductive Token where
  | a
  | b
  deriving DecidableEq

example : (naiveMatches [Token.a, Token.b] [Token.a, Token.b, Token.a, Token.b]).ret = [0, 2] := by
  rw [naiveMatches_ret]
  decide

private meta def verify (name : String) (pattern text expected : List Nat) (comparisons : Nat) :
    IO Unit := do
  let result := naiveMatches pattern text
  if result.ret != expected || result.time != comparisons then
    throw <| IO.userError s!"{name}: got {result.ret} with {result.time} comparisons"
  IO.println s!"{name}: shifts={result.ret}, comparisons={result.time}"

#eval do
  verify "CLRS Figure 32.3" [0, 0, 1] [0, 2, 0, 0, 1, 2] [2] 8
  verify "overlapping matches" [0, 0] [0, 0, 0] [0, 1] 4
  verify "matches separated by failure" [0, 1] [0, 1, 0, 1] [0, 2] 5
  verify "first-symbol mismatch" [1, 2] [0, 0, 0] [] 2
  verify "last-symbol mismatch" [0, 0, 1] [0, 0, 0, 0] [] 6
  verify "empty pattern boundaries" [] [0, 1] [0, 1, 2] 0
  verify "empty pattern and text" [] [] [0] 0
  verify "nonempty pattern, empty text" [0] [] [] 0
  verify "pattern longer than text" [0, 0] [0] [] 0
  verify "equal lengths" [0, 1] [0, 1] [0] 2
  verify "one-symbol pattern" [1] [1, 0, 1] [0, 2] 3
