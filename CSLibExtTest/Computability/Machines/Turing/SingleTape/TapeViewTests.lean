/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.TapeView
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.TapeView

@[expose] public section

/-!
# Tests for the view of CSLib tapes as Mathlib tapes

The cells of the view `BiTape.toTape` at integer positions, computed on input tapes and after
moves and writes, and compared with the cell formulas `nth_toTape`, `nth_toTape_mk₁`,
`nth_toTape_optionMove`, `nth_toTape_write_optionMove` and `nth_toTape_moveRight_iterate`.
-/

set_option autoImplicit false

open Turing Cslib.Turing

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape.TapeView

/-- The positions `-3, …, 3`. -/
def positions : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

/-- The cells `-3, …, 3` of the view, counted from the head. -/
def window (t : BiTape Bool) : List (Option Bool) :=
  positions.map t.toTape.nth

/-- The input tape of `true false true`. -/
def input : BiTape Bool := BiTape.mk₁ [true, false, true]

/-- A tape with non-blank cells on both sides of the head: two steps right on `input`, with a
blank written on the way. -/
def mixed : BiTape Bool := ((input.move .right).write none).move .right

/-! The input tape holds the word from the head on and blanks elsewhere. -/

#guard window input = [none, none, none, some true, some false, some true, none]

#guard window (BiTape.mk₁ []) = [none, none, none, none, none, none, none]

/-! A move shifts the cells, and a write changes the head cell only. -/

#guard window (input.move .right) = [none, none, some true, some false, some true, none, none]

#guard window (input.move .left) = [none, none, none, none, some true, some false, some true]

#guard window mixed = [none, some true, none, some true, none, none, none]

/-! Moving left off the input and back gives back the input tape: the blank pushed onto the right
half is dropped. -/

#guard let t := ((BiTape.mk₁ [true]).move .left).move .right
  t.head == some true && t.left.toList == [] && t.right.toList == []

/-! The general cell formula `nth_toTape`, on a tape with cells on both sides of the head. -/

#guard positions.all fun i ↦ mixed.toTape.nth i ==
  if i = 0 then mixed.head
  else if 0 < i then (mixed.right.toList[(i - 1).toNat]?).getD none
  else (mixed.left.toList[(-i - 1).toNat]?).getD none

/-! The input cell formula `nth_toTape_mk₁`. -/

#guard positions.all fun i ↦
  input.toTape.nth i == if 0 ≤ i then [true, false, true][i.toNat]? else none

/-! An optional move shifts the cells by `optionMoveOffset` (`nth_toTape_optionMove`), for each of
the three moves, and with a write first (`nth_toTape_write_optionMove`). -/

#guard [none, some Dir.left, some Dir.right].all fun d ↦ positions.all fun i ↦
  (mixed.optionMove d).toTape.nth i == mixed.toTape.nth (i + BiTape.optionMoveOffset d)

#guard [none, some Dir.left, some Dir.right].all fun d ↦ positions.all fun i ↦
  ((mixed.write (some false)).optionMove d).toTape.nth i ==
    if i + BiTape.optionMoveOffset d = 0 then some false
    else mixed.toTape.nth (i + BiTape.optionMoveOffset d)

/-! `n` moves right shift the cells by `n` (`nth_toTape_moveRight_iterate`). -/

#guard positions.all fun i ↦ (BiTape.moveRight^[2] input).toTape.nth i == input.toTape.nth (i + 2)

/-- The view of an input tape is the Mathlib input tape of its cells, by computation. -/
example : input.toTape = Tape.mk₁ [some true, some false, some true] :=
  rfl

/-- The view of `mixed`, by computation. -/
example : mixed.toTape =
    ⟨some true, ListBlank.mk [none, some true], ListBlank.mk []⟩ :=
  rfl

/-- `toTape_optionMove` on a left move: the view moves left. -/
example : (input.optionMove (some .left)).toTape = input.toTape.move .left := by
  rw [BiTape.toTape_optionMove]
  rfl

/-- The view distinguishes the input tapes of `[true]` and `[true, false]`, which differ only past
the head. -/
example : (BiTape.mk₁ [true]).toTape ≠ (BiTape.mk₁ [true, false]).toTape := fun h ↦
  absurd (congrArg (fun t ↦ t.right.toList) (BiTape.toTape_injective h))
    (by simp [BiTape.mk₁, StackTape.mapSome])

end CSLibExtTest.Computability.Machines.Turing.SingleTape.TapeView
