/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore

set_option autoImplicit false

open Cslib.Algorithms.Lean.TimeM

private meta def verify {σ : Nat} (name : String) (p t : List (Fin σ))
    (expected : List Nat) (events : Nat) : IO Unit := do
  let result := boyerMooreMatches p t
  if result.ret != expected || result.time != events then
    throw <| IO.userError s!"{name}: matches={result.ret}, events={result.time}"
  IO.println s!"{name}: matches={result.ret}, events={result.time}"

#eval do
  verify (σ := 26) "Lecroq gcagagag" [6, 2, 0, 6, 0, 6, 0, 6]
    [6, 2, 0, 19, 2, 6, 2, 0, 6, 0, 6, 0, 6, 19, 0, 19, 0, 2, 0, 6, 19, 0, 2, 6]
    [5] 156
  verify (σ := 1) "period-one overlaps" [0, 0, 0] [0, 0, 0, 0, 0, 0]
    [0, 1, 2, 3] 60
  verify (σ := 2) "period-two overlaps" [0, 1, 0] [0, 1, 0, 1, 0, 1, 0]
    [0, 2, 4] 55
  verify (σ := 2) "signed borrow boundary" [1, 0] [1, 1, 0] [1] 28
  verify (σ := 2) "negative bad-character proposal" [1, 0, 0] [0, 0, 0] [] 34
  verify (σ := 2) "best family, shift four" [0, 0, 0, 1]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [] 58
  verify (σ := 2) "last admissible offset" [0, 1] [1, 1, 0, 1] [2] 30
  verify (σ := 3) "whole text" [0, 1, 2] [0, 1, 2] [0] 36
  verify (σ := 3) "pattern longer than text" [0, 1, 2] [0, 1] [] 0
  verify (σ := 1) "nonempty pattern, empty text" [0] [] [] 0
  verify (σ := 2) "empty pattern, all boundaries" [] [0, 1, 0] [0, 1, 2, 3] 4
  verify (σ := 0) "empty alphabet" [] [] [0] 1
