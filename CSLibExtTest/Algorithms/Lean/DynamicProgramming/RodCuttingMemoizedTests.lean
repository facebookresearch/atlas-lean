/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCuttingMemoized

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat

public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCuttingMemoized
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Int.Defs
public meta import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-! Runtime checks for memoized rod cutting, including signed and fractional prices. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

private meta def checkCase {α : Type} [AddCommMonoid α] [LinearOrder α] [BEq α]
    [ToString α] {n : Nat} (label : String) (prices : Vector α n) (expected : α)
    (cache : Vector (Option α) (n + 1)) (time : Nat) : IO Unit := do
  let result := memoizedCutRodAux prices n le_rfl (Vector.replicate (n + 1) none)
  unless result.ret.1 == expected && result.ret.2 == cache && result.time == time do
    throw (IO.userError s!"{label}: got {result.ret.1}/{result.ret.2.toList}/{result.time}")
  let wrapper := memoizedCutRod prices
  unless wrapper.ret == expected && wrapper.time == time do
    throw (IO.userError s!"{label}: wrapper diverged from actual AUX")
  IO.println s!"{label}: value={result.ret.1} cache={result.ret.2.toList} time={result.time}"

private meta def runCases : IO Unit := do
  checkCase "empty" (#v[] : Vector Nat 0) 0 #v[some 0] 2
  checkCase "singleton" (#v[7] : Vector Nat 1) 7 #v[some 0, some 7] 5
  checkCase "signed singleton" (#v[-3] : Vector Int 1) (-3) #v[some 0, some (-3)] 5
  checkCase "CLRS four" (#v[1, 5, 8, 9] : Vector Nat 4) 10
    #v[some 0, some 1, some 5, some 8, some 10] 26
  checkCase "no cut" (#v[1, 2, 10] : Vector Int 3) 10
    #v[some 0, some 1, some 2, some 10] 17
  checkCase "ties" (#v[2, 4, 6] : Vector Nat 3) 6
    #v[some 0, some 2, some 4, some 6] 17
  checkCase "negative optimum" (#v[-2, -5, -9] : Vector Int 3) (-6)
    #v[some 0, some (-2), some (-4), some (-6)] 17
  checkCase "fractional" (#v[1 / 2, 7 / 4, 2] : Vector Rat 3) (9 / 4)
    #v[some 0, some (1 / 2), some (7 / 4), some (9 / 4)] 17
  checkCase "CLRS ten" (#v[1, 5, 8, 9, 10, 17, 17, 20, 24, 30] : Vector Nat 10) 30
    #v[some 0, some 1, some 5, some 8, some 10, some 13, some 17,
      some 18, some 22, some 25, some 30] 122
  let warm := memoizedCutRodAux (#v[1, 5, 8, 9] : Vector Nat 4) 4 le_rfl
    #v[some 0, some 1, some 5, some 8, none]
  unless warm.ret.1 == 10 && warm.time == 10 &&
      warm.ret.2 == #v[some 0, some 1, some 5, some 8, some 10] do
    throw (IO.userError "warm cache failed")
  IO.println "warm cache: value=10 cache=[0,1,5,8,10] time=10"
  let signed := memoizedCutRodAux (#v[-3] : Vector Int 1) 1 le_rfl #v[none, some (-3)]
  unless signed.ret.1 == -3 && signed.time == 1 && signed.ret.2 == #v[none, some (-3)] do
    throw (IO.userError "negative saved-cache hit failed")
  IO.println "negative saved hit: value=-3 unchanged cache time=1"
  let zero := memoizedCutRodAux (#v[] : Vector Nat 0) 0 le_rfl #v[some 7]
  unless zero.ret.1 == 7 && zero.time == 1 && zero.ret.2 == #v[some 7] do
    throw (IO.userError "cache was not checked before zero base case")
  IO.println "invalid zero saved hit: value=7 unchanged cache time=1"
  let validZero := memoizedCutRodAux (#v[] : Vector Nat 0) 0 le_rfl #v[some 0]
  unless validZero.ret.1 == 0 && validZero.time == 1 && validZero.ret.2 == #v[some 0] do
    throw (IO.userError "valid zero saved-cache hit failed")
  IO.println "valid zero saved hit: value=0 unchanged cache time=1"
  let shorterResult := memoizedCutRodAux (#v[1, 5, 8, 9] : Vector Nat 4) 2 (by decide)
    #v[none, none, none, some 999, some 888]
  unless shorterResult.ret.1 == 5 && shorterResult.time == 10 &&
      shorterResult.ret.2 == #v[some 0, some 1, some 5, some 999, some 888] do
    throw (IO.userError "partial target higher-cache frame failed")
  IO.println "partial target: value=5 higher cells999/888 unchanged time=10"
  IO.println "ACTUAL_U062_CASES 14"

#eval runCases
