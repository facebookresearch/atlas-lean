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

/-- **Half-tape view of a stack tape.** A stack tape $s$ over an alphabet $\Gamma$ is a finite list
of cells, each a symbol of $\Gamma$ or the blank cell, that does not end in a blank cell. Its
half-tape view is the half-tape of cells (a sequence of cells taken up to trailing blanks, the
blank cell being the default) whose cells are those of $s$ in order, followed by blank cells. -/
def toListBlank (s : StackTape Γ) : ListBlank (Option Γ) :=
  ListBlank.mk s.toList

/-- **Half-tape view of the empty stack tape.** The half-tape view of the empty stack tape over
$\Gamma$ is the half-tape all of whose cells are blank. -/
@[simp]
theorem toListBlank_nil : (nil : StackTape Γ).toListBlank = ListBlank.mk [] :=
  rfl

/-- **Pushing a cell onto a stack tape.** For every cell $c$ (a symbol of $\Gamma$ or the blank
cell) and every stack tape $s$ over $\Gamma$, the half-tape view of the stack tape obtained by
pushing $c$ onto $s$ is the half-tape view of $s$ with $c$ pushed onto its front.

For the blank cell this holds because the half-tape is blank beyond its end. -/
@[simp]
theorem toListBlank_cons (o : Option Γ) (s : StackTape Γ) :
    (cons o s).toListBlank = s.toListBlank.cons o := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rcases o with _ | a
  · exact (ListBlank.cons_head_tail (ListBlank.mk [])).symm
  all_goals rfl

/-- **First cell of the half-tape view of a stack tape.** For every stack tape $s$ over $\Gamma$
(a finite list of cells, each a symbol of $\Gamma$ or the blank, that does not end in a blank), the
first cell of the half-tape view of $s$ (its cells followed by infinitely many blanks) is the
first cell of $s$, which is the blank if $s$ is empty. -/
@[simp]
theorem head_toListBlank (s : StackTape Γ) : s.toListBlank.head = s.head := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rfl

/-- **Tail of the half-tape view of a stack tape.** For every stack tape $s$ over $\Gamma$ (a list
of cells, each a symbol of $\Gamma$ or the blank cell, not ending in a blank cell), the tail of
the half-tape view of $s$ is the half-tape view of the tail of $s$: dropping the first cell of
$s$ drops the first cell of its half-tape. -/
@[simp]
theorem tail_toListBlank (s : StackTape Γ) : s.toListBlank.tail = s.tail.toListBlank := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s <;> rfl

/-- **Cells of the half-tape view of a stack tape.** For every stack tape $s$ over $\Gamma$ (a
finite list of cells, each a symbol of $\Gamma$ or the blank, that does not end in a blank) and
every $n \in \mathbb{N}$, the cell at position $n$ of the half-tape view of $s$ (its cells followed
by infinitely many blanks) is the $n$-th cell of $s$, counting from $0$, if $n$ is less than the
length of $s$, and the blank otherwise. -/
theorem nth_toListBlank (s : StackTape Γ) (n : ℕ) :
    s.toListBlank.nth n = (s.toList[n]?).getD none :=
  List.getI_eq_getElem?_getD (l := s.toList) n

/-- **Half-tape view of a word.** For every word $a_1 \cdots a_n$ over $\Gamma$, the half-tape
view of the stack tape whose cells are the non-blank cells $a_1, \dots, a_n$ is the half-tape
whose first $n$ cells are $a_1, \dots, a_n$ and whose later cells are blank. -/
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

/-- **The half-tape view of stack tapes is injective.** If two stack tapes over $\Gamma$ have the
same half-tape view, then they are equal.

This holds because a stack tape does not end in a blank cell, so trailing blanks of a half-tape
do not come from cells. -/
theorem toListBlank_injective : Function.Injective (toListBlank (Γ := Γ)) := by
  rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
  rcases Quotient.exact h with h | h
  · cases eq_of_blankExtends h₂ h; rfl
  · cases eq_of_blankExtends h₁ h; rfl

end StackTape

namespace BiTape

/-- **Cell view of a two-way tape.** A CSLib tape $t$ over an alphabet $\Gamma$ has a head cell
and two halves, each a finite list of cells not ending in a blank, where a cell is a symbol of
$\Gamma$ or the blank. Its cell view is the Mathlib tape over cells, with the blank as default
symbol, whose head is the head cell of $t$ and whose left and right halves are the halves of $t$,
blank past their ends. So the cell at position $i \in \mathbb{Z}$ of the view is the cell $i$
places to the right of the head of $t$ (to the left when $i < 0$). -/
def toTape (t : BiTape Γ) : Tape (Option Γ) :=
  ⟨t.head, t.left.toListBlank, t.right.toListBlank⟩

/-- **Head cell of the view of a two-way tape.** For every two-way tape $t$ over $\Gamma$ (a head
cell with a left and a right stack tape), the head cell of the view of $t$ as a tape of cells is
the head cell of $t$. -/
@[simp]
theorem head_toTape (t : BiTape Γ) : t.toTape.head = t.head :=
  rfl

/-- **Left half of the view of a two-way tape.** For every two-way tape $t$ over $\Gamma$ (a head
cell with a left and a right stack tape), the left half of the view of $t$ as a tape of cells is
the half-tape view of the left stack tape of $t$. -/
@[simp]
theorem left_toTape (t : BiTape Γ) : t.toTape.left = t.left.toListBlank :=
  rfl

/-- **Right half of the tape view.** For every two-sided tape $t$ over $\Gamma$ (a head cell
together with a left and a right stack tape), the right half of the tape view of $t$ is the
half-tape view of the right half of $t$. -/
@[simp]
theorem right_toTape (t : BiTape Γ) : t.toTape.right = t.right.toListBlank :=
  rfl

/-- **The cells of the view.** Let $t$ be a two-way tape over $\Gamma$ with head cell $h$, left
stack tape $(\ell_0, \dots, \ell_{p-1})$ and right stack tape $(r_0, \dots, r_{q-1})$. For every
integer $i$, the cell at position $i$ of the view of $t$ as a tape of cells is $h$ if $i = 0$,
$r_{i-1}$ if $0 < i \le q$, $\ell_{-i-1}$ if $-p \le i < 0$, and the blank otherwise. -/
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

/-- **The cell view commutes with writing.** For every tape $t$ and every cell $a$ (a symbol or
the blank), the cell view of the tape obtained from $t$ by writing $a$ under the head equals the
tape obtained from the cell view of $t$ by writing $a$ under its head. -/
@[simp]
theorem toTape_write (t : BiTape Γ) (a : Option Γ) : (t.write a).toTape = t.toTape.write a :=
  rfl

/-- **The cell view commutes with head moves.** For every tape $t$ and each direction $d$ (left or
right), the cell view of the tape obtained from $t$ by moving the head one cell in direction $d$
equals the tape obtained from the cell view of $t$ by moving its head one cell in direction $d$. -/
@[simp]
theorem toTape_move (t : BiTape Γ) (d : Dir) : (t.move d).toTape = t.toTape.move d := by
  obtain ⟨a, L, R⟩ := t
  cases d <;> simp [toTape, move, moveLeft, moveRight, Tape.move]

/-- **The cell view commutes with optional head moves.** For every two-way tape $t$ over $\Gamma$
and every optional head move $d$, which is either no move or a move one cell in a direction, the
cell view of the tape obtained from $t$ by the optional move $d$ is the cell view of $t$ when $d$
is no move, and the cell view of $t$ with its head moved one cell in direction $d$ when $d$ is a
direction. -/
theorem toTape_optionMove (t : BiTape Γ) (d : Option Dir) :
    (t.optionMove d).toTape = d.elim t.toTape fun d ↦ t.toTape.move d := by
  cases d <;> simp [optionMove]

/-- **Offset of an optional head move.** The offset of an optional head move $d$ is $0$ if $d$ is
no move, $-1$ if $d$ is a move to the left and $1$ if $d$ is a move to the right.

After the move $d$, the cell at position $i$ relative to the head is the cell that was at
position $i$ plus the offset of $d$. -/
def optionMoveOffset : Option Dir → ℤ
  | none => 0
  | some .left => -1
  | some .right => 1

/-- **The offset of an optional move is at most one.** For every optional head move $d$ (no move,
a move to the left, or a move to the right), the offset of $d$ lies between $-1$ and $1$, that is,
$-1 \le \mathrm{offset}(d) \le 1$. -/
theorem optionMoveOffset_bound (d : Option Dir) :
    -1 ≤ optionMoveOffset d ∧ optionMoveOffset d ≤ 1 := by
  rcases d with _ | _ | _ <;> simp [optionMoveOffset]

/-- **Cells after a write.** For every two-way tape $t$ over $\Gamma$, every cell $a$ (a symbol of
$\Gamma$ or the blank) and every integer $i$, the cell at position $i$ of the view of the tape
obtained from $t$ by writing $a$ under the head is $a$ if $i = 0$, and the cell at position $i$
of the view of $t$ otherwise. -/
theorem nth_toTape_write (t : BiTape Γ) (a : Option Γ) (i : ℤ) :
    (t.write a).toTape.nth i = if i = 0 then a else t.toTape.nth i := by
  rw [toTape_write, Tape.write_nth]

/-- **Cells after an optional move.** For an optional direction $d$, let $\delta(d)$ be $0$ if $d$
is no move, $-1$ if $d$ is a move to the left and $1$ if $d$ is a move to the right. For every
two-way tape $t$ over $\Gamma$ and every integer $i$, the cell at position $i$ of the view of the
tape obtained from $t$ by the optional move $d$ is the cell at position $i + \delta(d)$ of the view
of $t$. -/
theorem nth_toTape_optionMove (t : BiTape Γ) (d : Option Dir) (i : ℤ) :
    (t.optionMove d).toTape.nth i = t.toTape.nth (i + optionMoveOffset d) := by
  rw [toTape_optionMove]
  rcases d with _ | _ | _
  · simp [optionMoveOffset]
  · rw [Option.elim_some, Tape.move_left_nth, optionMoveOffset, Int.sub_eq_add_neg]
  · rw [Option.elim_some, Tape.move_right_nth, optionMoveOffset]

/-- **Cells after a write and an optional move.** For an optional direction $d$, let $\delta(d)$ be
$0$ if $d$ is no move, $-1$ if $d$ is a move to the left and $1$ if $d$ is a move to the right. For
every two-way tape $t$ over $\Gamma$, every cell $a$ (a symbol of $\Gamma$ or the blank) and every
integer $i$, the cell at position $i$ of the view of the tape obtained from $t$ by writing $a$
under the head and then performing the optional move $d$ is $a$ if $i + \delta(d) = 0$, and the
cell at position $i + \delta(d)$ of the view of $t$ otherwise. -/
theorem nth_toTape_write_optionMove (t : BiTape Γ) (a : Option Γ) (d : Option Dir) (i : ℤ) :
    ((t.write a).optionMove d).toTape.nth i =
      if i + optionMoveOffset d = 0 then a else t.toTape.nth (i + optionMoveOffset d) := by
  rw [nth_toTape_optionMove, nth_toTape_write]

/-- **Cells after $n$ moves to the right.** For every two-way tape $t$ over $\Gamma$, every
$n \in \mathbb{N}$ and every integer $i$, the cell at position $i$ of the view of the tape obtained
from $t$ by moving the head $n$ times to the right is the cell at position $i + n$ of the view
of $t$. -/
theorem nth_toTape_moveRight_iterate (t : BiTape Γ) (n : ℕ) (i : ℤ) :
    (moveRight^[n] t).toTape.nth i = t.toTape.nth (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', show ∀ x : BiTape Γ, x.moveRight = x.move .right from
      fun _ ↦ rfl, toTape_move, Tape.move_right_nth, ih]
    congr 1
    omega

/-- **The cell view of an input tape.** For every word $w = w_0 w_1 \cdots w_{n-1}$ over $\Gamma$,
the cell view of the input tape of $w$ is the Mathlib input tape of the list of non-blank cells
$w_0, \dots, w_{n-1}$: the head is on $w_0$, the letters $w_1, \dots, w_{n-1}$ lie to its right
in order, and every other cell is blank (for the empty word, every cell is blank). -/
@[simp]
theorem toTape_mk₁ (l : List Γ) : (mk₁ l).toTape = Tape.mk₁ (l.map some) := by
  cases l with
  | nil => rfl
  | cons a l => simp [toTape, mk₁, Tape.mk₁, Tape.mk₂, Tape.mk']

/-- **Cells of an input tape.** For every word $w = w_0 \cdots w_{m-1}$ over $\Gamma$ and every
integer $i$, the cell at position $i$ of the view of the input tape of $w$ is $w_i$ if
$0 \le i < m$, and the blank otherwise. -/
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

/-- **The tape view is injective.** If two two-sided tapes $t$ and $t'$ over $\Gamma$ (each a head
cell together with a left and a right stack tape) have the same tape view as a tape of cells,
then $t = t'$. -/
theorem toTape_injective : Function.Injective (toTape (Γ := Γ)) := by
  rintro ⟨a₁, L₁, R₁⟩ ⟨a₂, L₂, R₂⟩ h
  simp only [toTape, Tape.mk.injEq] at h
  obtain ⟨rfl, hL, hR⟩ := h
  rw [StackTape.toListBlank_injective hL, StackTape.toListBlank_injective hR]

end BiTape

end Cslib.Turing
