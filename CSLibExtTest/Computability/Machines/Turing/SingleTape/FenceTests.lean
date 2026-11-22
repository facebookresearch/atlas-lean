/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Fence
public import CSLibExtTest.Computability.Machines.Turing.SingleTape.ClassesTests
public import CSLibExtTest.Computability.Machines.Turing.SingleTape.OfTM0Tests
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.Fence
public meta import CSLibExtTest.Computability.Machines.Turing.SingleTape.OfTM0Tests

@[expose] public section

/-!
# Tests for fenced single-tape machines

Two small machines: `rightTwice` moves right twice and halts, so it reads the cell of its start
and the cell to its right; `leftTwice` moves left twice and halts, so it reads the cell of its
start and the cell to its left. Their fenced machines are run on `fenceInput w i j` for small
paddings `i` (left) and `j` (right): they halt once the paddings hold the cells the machine reads,
and are trapped on a wall before. `rightTwice` needs right padding only, `leftTwice` left padding
only. Three inputs not of the shape `fenceInput w i j` show the other ways into the trap: on
`wall pad` the fenced `rightTwice` is trapped on the blank cell after the input (within the space
`n + 1` of an LBA), on `pad wall` it is trapped at once on the first cell, and on an input with a
wall inside it is trapped on that wall. The correctness and space theorems and the shape of fenced
inputs are applied to the two machines.
-/

set_option autoImplicit false

open Relation Computability Cslib.Turing Cslib.Turing.SingleTapeTM
open CSLibExtTest.Computability.Machines.Turing.SingleTape.OfTM0 (run)

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape.Fence

/-- Move right twice and halt. -/
def rightTwice : SingleTapeTM Bool where
  State := Fin 2
  q₀ := 0
  tr q c := (⟨c, some .right⟩, if q = 0 then some 1 else none)

/-- Move left twice and halt. -/
def leftTwice : SingleTapeTM Bool where
  State := Fin 2
  q₀ := 0
  tr q c := (⟨c, some .left⟩, if q = 0 then some 1 else none)

/-- The configuration of the fenced `tm` after `n` steps on the input `l`, or when it halts. -/
def runOn (tm : SingleTapeTM Bool) (l : List (FenceSymbol Bool)) (n : ℕ) : (fence tm).Cfg :=
  run (fence tm) n ((fence tm).initCfg l)

/-- The configuration of the fenced `tm` after `n` steps on `fenceInput w i j`, or when it
halts. -/
def runFence (tm : SingleTapeTM Bool) (w : List Bool) (i j n : ℕ) : (fence tm).Cfg :=
  runOn tm (fenceInput w i j) n

/-- A configuration of a fenced machine is halted. -/
def halted {tm : SingleTapeTM Bool} (c : (fence tm).Cfg) : Bool :=
  c.state.isNone

/-- A configuration of a fenced machine is in the trap. -/
def trapped {tm : SingleTapeTM Bool} (c : (fence tm).Cfg) : Bool :=
  match c.state with
  | some .trap => true
  | _ => false

/-- The position of the head of a configuration of a fenced machine, counted from the first cell
of the input: the number of cells to its left, the input having no blank cell. -/
def headPos {tm : SingleTapeTM Bool} (c : (fence tm).Cfg) : ℕ :=
  c.BiTape.left.toList.length

/-! On the empty word, `rightTwice` reads the cells `0` and `1` of the word, both right padding:
the fenced machine halts with two cells of right padding, whatever the left padding, and is
trapped with fewer. -/

#guard (List.range 4).map (fun j ↦ halted (runFence rightTwice [] 0 j 20)) =
  [false, false, true, true]

#guard (List.range 4).map (fun j ↦ trapped (runFence rightTwice [] 2 j 20)) =
  [true, true, false, false]

/-! With one cell of padding on each side, the input is `wall lpad pad wall`: the fenced machine
steps off the left wall and over `lpad` to the `pad` at position `2`, moves right onto the right
wall at position `3`, and is trapped there. -/

#guard let c := runFence rightTwice [] 1 1 20
  trapped c && c.BiTape.head == some .wall && headPos c == 3

/-! The fenced machine halts in as many steps as the start phase and `rightTwice`: one step off the
left wall, `i` steps over the left padding, and the two steps of `rightTwice`. -/

#guard !halted (runFence rightTwice [true, false] 3 1 5) &&
  halted (runFence rightTwice [true, false] 3 1 6)

/-! `leftTwice` reads the cell to the left of its start, which is the left wall without left
padding: one cell of left padding is enough, with no right padding. -/

#guard (List.range 3).map (fun i ↦ halted (runFence leftTwice [true, true] i 0 20)) =
  [false, true, true]

#guard let c := runFence leftTwice [true, true] 0 3 20
  trapped c && c.BiTape.head == some .wall && headPos c == 0

/-! On `wall pad`, which is not of the shape `fenceInput w i j`, the fenced `rightTwice` steps off
the wall onto `pad`, runs `rightTwice` there, and moves right onto the blank cell after the input,
where it is trapped. That configuration uses `3 = n + 1` cells on the input of length `n = 2`, the
bound of `IsLBA`. -/

#guard let c := runOn rightTwice [.wall, .pad] 20
  trapped c && c.BiTape.head == none && headPos c == 2 && c.spaceUsed == 3

/-! On `pad wall`, the initial state reads a cell other than a wall and enters the trap at once,
leaving the head on the first cell. -/

#guard let c := runOn rightTwice [.pad, .wall] 20
  trapped c && c.BiTape.head == some .pad && headPos c == 0 && c.spaceUsed == 2

/-! On `wall (sym true) wall pad wall`, the fenced `rightTwice` steps off the left wall onto
`sym true`, takes the first step of `rightTwice` there, and is trapped on the inner wall at
position `2`, before the padding behind it. -/

#guard let c := runOn rightTwice [.wall, .sym true, .wall, .pad, .wall] 20
  trapped c && c.BiTape.head == some .wall && headPos c == 2

/-! ### The theorems on the two machines -/

/-- `rightTwice` halts on every input. -/
theorem rightTwice_haltsOn (w : List Bool) : rightTwice.HaltsOn w :=
  ⟨_, .head rfl (.head rfl .refl), rfl⟩

/-- `leftTwice` halts on every input. -/
theorem leftTwice_haltsOn (w : List Bool) : leftTwice.HaltsOn w :=
  ⟨_, .head rfl (.head rfl .refl), rfl⟩

/-- With two cells of right padding, the fenced `rightTwice` halts on the empty word, in three
steps: one off the left wall and the two steps of `rightTwice`. -/
theorem fence_rightTwice_haltsOn : (fence rightTwice).HaltsOn (fenceInput [] 0 2) :=
  ⟨_, .head rfl (.head rfl (.head rfl .refl)), rfl⟩

example : (fence rightTwice).IsLBA :=
  isLBA_fence _

example : (fence leftTwice).IsLBA :=
  isLBA_fence _

/-- The correctness theorem finds paddings for every word. -/
example (w : List Bool) : ∃ i j, (fence leftTwice).HaltsOn (fenceInput w i j) :=
  (exists_haltsOn_fence_iff _ _).2 (leftTwice_haltsOn w)

/-- Conversely, a halting fenced run gives a halting run of `rightTwice`. -/
example : rightTwice.HaltsOn [] :=
  (exists_haltsOn_fence_iff _ _).1 ⟨0, 2, fence_rightTwice_haltsOn⟩

/-- The shape of a fenced input: its length, and the right wall at its last cell. -/
example : (fenceInput [true, false] 1 3).length = 8 ∧
    (fenceInput [true, false] 1 3)[7]? = some .wall := by
  refine ⟨by simp, ?_⟩
  rw [getElem?_fenceInput]
  rfl

/-- A machine that never halts has a fenced machine that halts on no padding. -/
example (w : List Bool) : ∀ i j, ¬(fence loopForever).HaltsOn (fenceInput w i j) :=
  (forall_not_haltsOn_fence_iff _ _).2 (not_loopForever_haltsOn w)

end CSLibExtTest.Computability.Machines.Turing.SingleTape.Fence
