/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Int.Defs
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Extended rod-cutting tables and reconstruction runtime tests

Each case checks every saved revenue and first cut, the emitted ordered blocks, their revenue,
both actual event counts, and the saved-entry trace. Assertions throw on mismatch.
The CLRS printed tables and the length-seven output distinguish emitted order from reversal.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

private meta def checkReconstruction {α : Type} [AddCommMonoid α] [LinearOrder α]
    [BEq α] [LawfulBEq α] [ToString α] {n : Nat} (name : String) (prices : Vector α n)
    (rows : List α) (cuts blocks : List Nat) (revenue : α)
    (tableEvents solutionEvents : Nat) : IO Unit := do
  let tables := extendedBottomUpCutRod prices
  unless tables.ret.1.toList == rows && tables.ret.2.toList == cuts do
    throw (IO.userError s!"{name}: saved tables differ: r={tables.ret.1.toList}, s={tables.ret.2.toList}")
  unless tables.time == tableEvents do
    throw (IO.userError s!"{name}: table events {tables.time}, expected {tableEvents}")
  let result := cutRodSolution prices
  unless result.ret.blocks == blocks do
    throw (IO.userError s!"{name}: emitted {result.ret.blocks}, expected {blocks}")
  let earned := compositionRevenue prices result.ret le_rfl
  unless earned == revenue do
    throw (IO.userError s!"{name}: earned {earned}, expected {revenue}")
  unless result.time == solutionEvents do
    throw (IO.userError s!"{name}: solution events {result.time}, expected {solutionEvents}")
  for i in [:result.ret.length] do
    unless tables.ret.2[n - result.ret.sizeUpTo i - 1]? == result.ret.blocks[i]? do
      throw (IO.userError s!"{name}: saved-entry trace differs at emitted block {i}")
  IO.println s!"{name}: r={tables.ret.1.toList}, s={tables.ret.2.toList}, pieces={result.ret.blocks}, revenue={earned}, events={tables.time}/{result.time}"

#eval checkReconstruction "empty" (#v[] : Vector Nat 0) [0] [] [] 0 0 0
#eval checkReconstruction "single positive" (#v[7] : Vector Nat 1) [0, 7] [1] [1] 7 1 2
#eval checkReconstruction "single zero" (#v[0] : Vector Nat 1) [0, 0] [1] [1] 0 1 2
#eval checkReconstruction "repeated unit pieces" (#v[2, 3] : Vector Nat 2)
  [0, 2, 4] [1, 1] [1, 1] 4 3 5
#eval checkReconstruction "strict earliest tie" (#v[1, 2] : Vector Nat 2)
  [0, 1, 2] [1, 1] [1, 1] 2 3 5
#eval checkReconstruction "multiple equal candidates" (#v[1, 2, 3, 4] : Vector Nat 4)
  [0, 1, 2, 3, 4] [1, 1, 1, 1] [1, 1, 1, 1] 4 10 14
#eval checkReconstruction "largest cut improves" (#v[1, 1, 8] : Vector Nat 3)
  [0, 1, 2, 8] [1, 1, 3] [3] 8 6 7
#eval checkReconstruction "CLRS length four" (#v[1, 5, 8, 9] : Vector Nat 4)
  [0, 1, 5, 8, 10] [1, 2, 3, 2] [2, 2] 10 10 12
#eval checkReconstruction "CLRS full tables" (#v[1, 5, 8, 9, 10, 17, 17, 20, 24, 30] : Vector Nat 10)
  [0, 1, 5, 8, 10, 13, 17, 18, 22, 25, 30] [1, 2, 3, 2, 2, 6, 1, 2, 3, 10] [10] 30 55 56
#eval checkReconstruction "CLRS emitted order" (#v[1, 5, 8, 9, 10, 17, 17] : Vector Nat 7)
  [0, 1, 5, 8, 10, 13, 17, 18] [1, 2, 3, 2, 2, 6, 1] [1, 6] 18 28 30
#eval checkReconstruction "single negative, no discard" (#v[-2] : Vector Int 1)
  [0, -2] [1] [1] (-2) 1 2
#eval checkReconstruction "negative optimum" (#v[-2, -5, -9] : Vector Int 3)
  [0, -2, -4, -6] [1, 1, 1] [1, 1, 1] (-6) 6 9
#eval checkReconstruction "no-cut optimum" (#v[-5, 10] : Vector Int 2)
  [0, -5, 10] [1, 2] [2] 10 3 4
#eval checkReconstruction "zero with negative alternatives" (#v[0, -1, -10] : Vector Int 3)
  [0, 0, 0, 0] [1, 1, 1] [1, 1, 1] 0 6 9
#eval checkReconstruction "fractional prices" (#v[1 / 2, 3 / 4] : Vector Rat 2)
  [0, 1 / 2, 1] [1, 1] [1, 1] 1 3 5
