/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Data.BiTape

/-!
# CSLib tapes as Mathlib tapes

CSLib's single-tape machines run on a `Cslib.Turing.BiTape Γ`: a head cell and two
`Cslib.Turing.StackTape Γ` halves, lists of cells `Option Γ` that do not end in a blank, the
cells past their ends being blank. Mathlib's `Turing.Tape Γ'` is a head symbol and two
`Turing.ListBlank Γ'` halves, lists up to trailing `default` symbols. This file reads a CSLib tape
as a Mathlib tape of cells, `BiTape.toTape : BiTape Γ → Turing.Tape (Option Γ)`, with the blank
cell `none` as the default symbol. Moves, writes and input tapes correspond (`BiTape.toTape_move`,
`BiTape.toTape_write`, `BiTape.toTape_mk₁`), so statements about cells at integer positions
(`Turing.Tape.nth`) transfer to CSLib tapes. The view is injective (`BiTape.toTape_injective`),
because a `StackTape` does not end in a blank.

A Mathlib tape over another alphabet with a blank symbol is obtained by `Turing.Tape.map` of a
pointed map, as in `SingleTapeTM.toTape` of `OfTM0`.

## Main definitions

- `Cslib.Turing.StackTape.toListBlank`, `Cslib.Turing.BiTape.toTape`.
- `Cslib.Turing.BiTape.optionMoveOffset`: the shift of the cells under an optional move.

## Main results

- `Cslib.Turing.BiTape.nth_toTape`: the cells of the view.
- `Cslib.Turing.BiTape.toTape_move`, `Cslib.Turing.BiTape.toTape_write`,
  `Cslib.Turing.BiTape.toTape_optionMove`, `Cslib.Turing.BiTape.toTape_mk₁`: the view commutes
  with the tape operations; `Cslib.Turing.BiTape.nth_toTape_write_optionMove`,
  `Cslib.Turing.BiTape.nth_toTape_moveRight_iterate`, `Cslib.Turing.BiTape.nth_toTape_mk₁`: the
  cells after them.
- `Cslib.Turing.StackTape.toListBlank_injective`, `Cslib.Turing.BiTape.toTape_injective`.
-/

@[expose] public section

set_option autoImplicit false

open _root_.Turing

namespace Cslib.Turing

variable {Γ : Type*}

namespace StackTape

/-- A `StackTape` read as a Mathlib half-tape of cells: the cells past the end of the list are
blank, and the blank cell `none` is the default symbol. -/
def toListBlank (s : StackTape Γ) : ListBlank (Option Γ) :=
  ListBlank.mk s.toList

/-- The empty `StackTape` reads as the all-blank half-tape. -/
@[simp]
theorem toListBlank_nil : (nil : StackTape Γ).toListBlank = ListBlank.mk [] :=
  rfl

/-- Pushing a cell onto a `StackTape` pushes it onto the half-tape; for the blank cell this holds
because the half-tape is blank beyond its end. -/
@[simp]
theorem toListBlank_cons (o : Option Γ) (s : StackTape Γ) :
    (cons o s).toListBlank = s.toListBlank.cons o := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rcases o with _ | a
  · exact (ListBlank.cons_head_tail (ListBlank.mk [])).symm
  all_goals rfl

/-- The first cell of the half-tape is the first cell of the `StackTape`. -/
@[simp]
theorem head_toListBlank (s : StackTape Γ) : s.toListBlank.head = s.head := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rfl

/-- Dropping the first cell of a `StackTape` drops the first cell of the half-tape. -/
@[simp]
theorem tail_toListBlank (s : StackTape Γ) : s.toListBlank.tail = s.tail.toListBlank := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rfl

/-- The cell at position `n` of the half-tape is the `n`-th cell of the `StackTape`, blank past
its end. -/
theorem nth_toListBlank (s : StackTape Γ) (n : ℕ) :
    s.toListBlank.nth n = (s.toList[n]?).getD none :=
  List.getI_eq_getElem?_getD (l := s.toList) n

/-- A word laid out as non-blank cells reads as its cells. -/
@[simp]
theorem toListBlank_mapSome (l : List Γ) :
    (mapSome l).toListBlank = ListBlank.mk (l.map some) :=
  rfl

/-- Two lists of cells, the second not ending in a blank, that agree up to trailing blanks are
equal. -/
private theorem eq_of_blankExtends {l₁ l₂ : List (Option Γ)} (h₂ : l₂.getLast? ≠ some none)
    (h : BlankExtends l₁ l₂) : l₁ = l₂ := by
  obtain ⟨_ | n, rfl⟩ := h
  · simp
  · exfalso
    apply h₂
    simp [List.getLast?_append, List.getLast?_replicate]
    rfl

/-- `toListBlank` is injective: a `StackTape` does not end in a blank, so trailing blanks of a
half-tape do not come from cells. -/
theorem toListBlank_injective : Function.Injective (toListBlank (Γ := Γ)) := by
  rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
  rcases Quotient.exact h with h | h
  · cases eq_of_blankExtends h₂ h; rfl
  · cases eq_of_blankExtends h₁ h; rfl

end StackTape

namespace BiTape

/-- A `BiTape` read as a Mathlib tape of cells, the blank cell `none` being the default symbol:
the cell at position `i` of the view (`Turing.Tape.nth`) is the cell `i` places to the right of
the head (`BiTape.nth_toTape`). -/
def toTape (t : BiTape Γ) : Tape (Option Γ) :=
  ⟨t.head, t.left.toListBlank, t.right.toListBlank⟩

/-- The head cell of the view is the head cell of the tape. -/
@[simp]
theorem head_toTape (t : BiTape Γ) : t.toTape.head = t.head :=
  rfl

/-- The left half of the view is the half-tape of the left half. -/
@[simp]
theorem left_toTape (t : BiTape Γ) : t.toTape.left = t.left.toListBlank :=
  rfl

/-- The right half of the view is the half-tape of the right half. -/
@[simp]
theorem right_toTape (t : BiTape Γ) : t.toTape.right = t.right.toListBlank :=
  rfl

/-- **The cells of the view**: the head cell at position `0`, the cells of the right half at the
positive positions, and the cells of the left half at the negative positions, blank past the ends
of the halves. -/
theorem nth_toTape (t : BiTape Γ) (i : ℤ) :
    t.toTape.nth i =
      if i = 0 then t.head
      else if 0 < i then (t.right.toList[(i - 1).toNat]?).getD none
      else (t.left.toList[(-i - 1).toNat]?).getD none := by
  rcases i with (_ | n) | n
  · rfl
  · change t.right.toListBlank.nth n = _
    rw [Int.ofNat_eq_natCast, StackTape.nth_toListBlank, ite_eq_right (by omega),
      ite_eq_left (by omega)]
    congr 3
    omega
  · change t.left.toListBlank.nth n = _
    rw [Int.negSucc_eq, StackTape.nth_toListBlank, ite_eq_right (by omega),
      ite_eq_right (by omega)]
    congr 3
    omega

/-- The view turns writing a cell into writing it. -/
@[simp]
theorem toTape_write (t : BiTape Γ) (a : Option Γ) : (t.write a).toTape = t.toTape.write a :=
  rfl

/-- The view commutes with moving the head. -/
@[simp]
theorem toTape_move (t : BiTape Γ) (d : Dir) : (t.move d).toTape = t.toTape.move d := by
  obtain ⟨a, L, R⟩ := t
  cases d <;> simp [toTape, move, moveLeft, moveRight, Tape.move]

/-- The view commutes with an optional move of the head. -/
theorem toTape_optionMove (t : BiTape Γ) (d : Option Dir) :
    (t.optionMove d).toTape = d.elim t.toTape fun d ↦ t.toTape.move d := by
  cases d <;> simp [optionMove]

/-- The offset of an optional move: after the move, the cell at position `i` is the cell that was
at position `i + optionMoveOffset d`. -/
def optionMoveOffset : Option Dir → ℤ
  | none => 0
  | some .left => -1
  | some .right => 1

/-- An optional move shifts by at most one cell. -/
theorem optionMoveOffset_bound (d : Option Dir) :
    -1 ≤ optionMoveOffset d ∧ optionMoveOffset d ≤ 1 := by
  rcases d with _ | _ | _ <;> simp [optionMoveOffset]

/-- The cells after a write: the head cell is the written cell, the others are unchanged. -/
theorem nth_toTape_write (t : BiTape Γ) (a : Option Γ) (i : ℤ) :
    (t.write a).toTape.nth i = if i = 0 then a else t.toTape.nth i := by
  rw [toTape_write, Tape.write_nth]

/-- The cells after an optional move are those before, shifted by `optionMoveOffset`. -/
theorem nth_toTape_optionMove (t : BiTape Γ) (d : Option Dir) (i : ℤ) :
    (t.optionMove d).toTape.nth i = t.toTape.nth (i + optionMoveOffset d) := by
  rw [toTape_optionMove]
  rcases d with _ | _ | _
  · simp [optionMoveOffset]
  · rw [Option.elim_some, Tape.move_left_nth, optionMoveOffset, Int.sub_eq_add_neg]
  · rw [Option.elim_some, Tape.move_right_nth, optionMoveOffset]

/-- The cells after a write and an optional move, the form of a machine step. -/
theorem nth_toTape_write_optionMove (t : BiTape Γ) (a : Option Γ) (d : Option Dir) (i : ℤ) :
    ((t.write a).optionMove d).toTape.nth i =
      if i + optionMoveOffset d = 0 then a else t.toTape.nth (i + optionMoveOffset d) := by
  rw [nth_toTape_optionMove, nth_toTape_write]

/-- The cells after `n` moves to the right are those before, shifted by `n`. -/
theorem nth_toTape_moveRight_iterate (t : BiTape Γ) (n : ℕ) (i : ℤ) :
    (moveRight^[n] t).toTape.nth i = t.toTape.nth (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', show ∀ x : BiTape Γ, x.moveRight = x.move .right from
      fun _ ↦ rfl, toTape_move, Tape.move_right_nth, ih]
    congr 1
    omega

/-- The input tape of a word reads as the Mathlib input tape of its cells. -/
@[simp]
theorem toTape_mk₁ (l : List Γ) : (mk₁ l).toTape = Tape.mk₁ (l.map some) := by
  cases l with
  | nil => rfl
  | cons a l => simp [toTape, mk₁, Tape.mk₁, Tape.mk₂, Tape.mk']

/-- The cells of an input tape: the word from position `0` on, blank elsewhere. -/
theorem nth_toTape_mk₁ (l : List Γ) (i : ℤ) :
    (mk₁ l).toTape.nth i = if 0 ≤ i then l[i.toNat]? else none := by
  rcases i with (_ | n) | n
  · cases l <;> rfl
  · cases l with
    | nil => rfl
    | cons a r =>
      change (ListBlank.mk (r.map some)).nth n =
        if 0 ≤ ((n + 1 : ℕ) : ℤ) then (a :: r)[((n + 1 : ℕ) : ℤ).toNat]? else none
      rw [ite_eq_left (by omega), Int.toNat_natCast, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
        List.getElem?_cons_succ, List.getElem?_map]
      cases r[n]? <;> rfl
  · cases l <;> rfl

/-- The view is injective. -/
theorem toTape_injective : Function.Injective (toTape (Γ := Γ)) := by
  rintro ⟨a₁, L₁, R₁⟩ ⟨a₂, L₂, R₂⟩ h
  simp only [toTape, Tape.mk.injEq] at h
  obtain ⟨rfl, hL, hR⟩ := h
  rw [StackTape.toListBlank_injective hL, StackTape.toListBlank_injective hR]

end BiTape

end Cslib.Turing
