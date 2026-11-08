/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Preprocessing

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.StringMatching.BoyerMoore

private meta def verify {σ m : Nat} (name : String) (p : Vector (Fin σ) m)
    (bad good : List Nat) (fills : Nat) : IO Unit := do
  let result := preprocess p
  let events := if m = 0 then σ else σ + 6 * m - 2 + fills + (computeZ p.reverse).time
  let bound := if m = 0 then σ else σ + 10 * m - 6
  if result.ret.1.toList != bad || result.ret.2.toList != good ||
      result.time != events || bound < result.time then
    let actual := s!"bad={result.ret.1.toList}, good={result.ret.2.toList}"
    throw <| IO.userError s!"{name}: {actual}, events={result.time}, expected={events}"
  IO.println s!"{name}: good={result.ret.2.toList}, events={result.time}, fills={fills}"

#eval do
  verify (σ := 0) "empty alphabet and pattern" #v[] [] [] 0
  verify (σ := 3) "empty finite pattern" #v[] [0, 0, 0] [] 0
  verify (σ := 3) "singleton, excluded last occurrence" #v[1] [1, 1, 1] [1] 0
  verify (σ := 1) "aa strong predecessor endpoint" #v[0, 0] [1] [1, 2] 1
  verify (σ := 1) "period-one overlap" #v[0, 0, 0, 0] [1] [1, 2, 3, 4] 3
  verify (σ := 2) "ba absent-before-last" #v[1, 0] [2, 1] [2, 1] 0
  verify (σ := 4) "distinct symbols, default shifts" #v[0, 1, 2, 3]
    [3, 2, 1, 4] [4, 4, 4, 1] 0
  verify (σ := 2) "ababa repeated border fills" #v[0, 1, 0, 1, 0]
    [2, 1] [2, 2, 4, 4, 1] 4
  verify (σ := 3) "abcab nontrivial period" #v[0, 1, 2, 0, 1]
    [1, 3, 2] [3, 3, 3, 5, 1] 3
  verify (σ := 2) "abaa internal strong recurrence" #v[0, 1, 0, 0]
    [1, 2] [3, 3, 1, 2] 3
  verify (σ := 26) "Lecroq gcagagag" #v[6, 2, 0, 6, 0, 6, 0, 6]
    [1, 8, 6, 8, 8, 8, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]
    [7, 7, 7, 2, 7, 4, 7, 1] 7
  verify (σ := 24) "original ABCXXXABC" #v[0, 1, 2, 23, 23, 23, 0, 1, 2]
    [2, 1, 6, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 3]
    [6, 6, 6, 6, 6, 6, 9, 9, 1] 6
  verify (σ := 25) "original ABYXCDEYX" #v[0, 1, 24, 23, 2, 3, 4, 24, 23]
    [8, 7, 4, 3, 2, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 5, 1]
    [9, 9, 9, 9, 9, 9, 5, 9, 1] 0
