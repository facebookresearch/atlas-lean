/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RecursiveRodCutting
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Int.Defs
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

private def checkCase {α : Type} [AddCommMonoid α] [LinearOrder α] [BEq α] [ToString α]
    {n : Nat} (name : String) (prices : Vector α n) (expected : α) (calls : Nat) :
    IO Unit := do
  let result := recursiveCutRod prices
  unless result.ret == expected && result.time == calls do
    throw (IO.userError s!"{name}: actual {result.ret}/{result.time}; expected {expected}/{calls}")
  IO.println s!"{name}: revenue={result.ret}, calls={result.time}"

#eval checkCase "empty" (#v[] : Vector Nat 0) 0 1
#eval checkCase "singleton" (#v[7] : Vector Nat 1) 7 2
#eval checkCase "zero singleton" (#v[0] : Vector Nat 1) 0 2
#eval checkCase "unit cuts" (#v[2, 3] : Vector Nat 2) 4 4
#eval checkCase "CLRS four" (#v[1, 5, 8, 9] : Vector Nat 4) 10 16
#eval checkCase "CLRS chart" (#v[1, 5, 8, 9, 10, 17, 17, 20, 24, 30] : Vector Nat 10) 30 1024
#eval checkCase "negative singleton" (#v[-2] : Vector Int 1) (-2) 2
#eval checkCase "all negative" (#v[-2, -5, -9] : Vector Int 3) (-6) 8
#eval checkCase "no cut" (#v[-5, 10] : Vector Int 2) 10 4
#eval checkCase "negative alternatives" (#v[0, -1, -10] : Vector Int 3) 0 8
#eval checkCase "fractional" (#v[1 / 2, 3 / 4] : Vector Rat 2) 1 4
