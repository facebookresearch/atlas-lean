/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.StringMatching.ZAlgorithm
public meta import Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching

private meta def verify {n : Nat} (name : String) (input : Vector Nat n)
    (expected : List Nat) (events : Nat) : IO Unit := do
  let result := computeZ input
  if result.ret.toList != expected || result.time != events then
    throw <| IO.userError s!"{name}: got {result.ret.toList} with {result.time} events"
  IO.println s!"{name}: Z={result.ret.toList}, events={result.time}"

#eval do
  verify "empty" #v[] [] 0
  verify "singleton" #v[0] [1] 0
  verify "repeated endpoint" #v[0, 0, 0, 0] [4, 3, 2, 1] 6
  verify "outside first-symbol failures" #v[0, 1, 2, 3] [4, 0, 0, 0] 6
  verify "overlapping periodic suffixes" #v[0, 1, 0, 1, 0] [5, 0, 3, 0, 1] 8
  verify "Gusfield copy and extension" #v[0, 0, 1, 2, 0, 0, 1, 3, 0, 0, 4]
    [11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0] 24
  verify "greater-seed explicit failure" #v[0, 0, 0, 0, 1] [5, 3, 2, 1, 0] 11
  verify "copy shorter than box" #v[0, 1, 0, 1, 2, 0, 1, 0, 1, 3]
    [10, 0, 2, 0, 0, 4, 0, 2, 0, 0] 21
  verify "equal-seed success then exhaustion" #v[0, 0, 1, 0, 0, 0, 1]
    [7, 1, 0, 2, 3, 1, 0] 14
  verify "equal-seed success then failure" #v[0, 0, 1, 0, 0, 0, 1, 2]
    [8, 1, 0, 2, 3, 1, 0, 0] 17
