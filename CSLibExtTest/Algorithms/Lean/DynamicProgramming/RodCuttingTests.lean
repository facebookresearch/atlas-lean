/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Int.Defs
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Rod-cutting boundary and public-interface tests

The runtime assertions execute the public solver, including its private saved-table code.
Closed mathematical examples use ordinary `decide`; correctness and cost are also exercised
through named public theorems without exposing the implementation.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

private def clrsPrices : Vector Nat 10 := #v[1, 5, 8, 9, 10, 17, 17, 20, 24, 30]
private def fourPrices : Vector Nat 4 := #v[1, 5, 8, 9]
private def signedPrices : Vector Int 3 := #v[-2, -5, -9]
private def fractionalPrices : Vector Rat 2 := #v[1 / 2, 3 / 4]

private def checkCase {α : Type} [AddCommMonoid α] [LinearOrder α] [BEq α] [ToString α]
    {n : Nat} (name : String) (prices : Vector α n) (expected : α) (ticks : Nat) : IO Unit := do
  let result := bottomUpCutRod prices
  unless result.ret == expected && result.time == ticks do
    throw (IO.userError s!"{name}: got revenue {result.ret}, ticks {result.time}; expected {expected}, {ticks}")
  IO.println s!"{name}: revenue={result.ret}, ticks={result.time}"

#eval checkCase "empty" (#v[] : Vector Nat 0) 0 0
#eval checkCase "single positive" (#v[7] : Vector Nat 1) 7 1
#eval checkCase "single zero" (#v[0] : Vector Nat 1) 0 1
#eval checkCase "repeated unit pieces" (#v[2, 3] : Vector Nat 2) 4 3
#eval checkCase "CLRS length four" fourPrices 10 10
#eval checkCase "CLRS full chart" clrsPrices 30 55
#eval checkCase "single negative, no discard" (#v[-2] : Vector Int 1) (-2) 1
#eval checkCase "negative optimum" signedPrices (-6) 6
#eval checkCase "no-cut optimum" (#v[-5, 10] : Vector Int 2) 10 3
#eval checkCase "zero with negative alternatives" (#v[0, -1, -10] : Vector Int 3) 0 6
#eval checkCase "fractional prices" fractionalPrices 1 3

example : compositionRevenue (#v[] : Vector Nat 0) (Composition.ones 0) le_rfl = 0 := by
  decide

example : compositionRevenue (#v[7] : Vector Nat 1) (Composition.single 1 (by decide))
    le_rfl = 7 := by decide

example : compositionRevenue fourPrices (⟨[2, 2], by decide, by decide⟩ : Composition 4)
    le_rfl = 10 := by decide

example : compositionRevenue clrsPrices (⟨[1, 6], by decide, by decide⟩ : Composition 7)
    (by decide) = 18 := by decide

example : compositionRevenue signedPrices (Composition.ones 3) le_rfl = -6 := by decide

example : compositionRevenue fractionalPrices (Composition.ones 2) le_rfl = 1 := by
  change compositionRevenue fractionalPrices
    ((Composition.single 1 (by decide)).append (Composition.single 1 (by decide))) le_rfl = 1
  rw [compositionRevenue_append, compositionRevenue_single]
  change (1 / 2 : Rat) + 1 / 2 = 1
  norm_num

example : ¬ ∃ parts : Composition 3, parts.blocks = [0, 3] := by
  rintro ⟨parts, hparts⟩
  have hpositive := parts.blocks_pos (show 0 ∈ parts.blocks by simp [hparts])
  omega

example : ¬ ∃ parts : Composition 3, parts.blocks = [1, 1] := by
  rintro ⟨parts, hparts⟩
  have htotal := parts.blocks_sum
  simp [hparts] at htotal

example : (bottomUpCutRod clrsPrices).time = 55 := by
  rw [bottomUpCutRod_time]

example : (bottomUpCutRod (#v[] : Vector Int 0)).ret = 0 := by simp

example (prices : Vector Int 8) :
    IsGreatest (Set.range fun parts : Composition 8 => compositionRevenue prices parts le_rfl)
      (bottomUpCutRod prices).ret := bottomUpCutRod_correct prices

example (prices : Vector Nat 8) :
    64 ≤ 2 * (bottomUpCutRod prices).time ∧ (bottomUpCutRod prices).time ≤ 64 :=
  bottomUpCutRod_time_bounds prices

example (prices : Vector Rat 8) : (bottomUpCutRod prices).time = 36 := by
  rw [bottomUpCutRod_time]
