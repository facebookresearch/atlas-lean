/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.SpaceBounded

/-!
# Fenced single-tape machines; emptiness of an LBA on computable input slices is undecidable

For a single-tape machine `tm`, the **fenced machine** `fence tm` runs `tm` between two end
markers. Its input `fenceInput w i j` is the word `w` with `i` padding cells on the left and `j`
on the right, between two walls:

  `wall, lpad, …, lpad, w₁, …, wₙ, pad, …, pad, wall`.

`fence tm` starts on the left wall and moves right off it, steps right over the left padding, and
then runs `tm` from its initial state on the first cell after the padding, reading padding cells
as blanks and writing a blank as `pad`. From then on it enters a trap state, which loops forever,
whenever it reads a wall or a blank cell; in its initial state it enters the trap on any cell
other than a wall. So on a blank cell, in every state, it writes a blank and does not move, and
it is a linear bounded automaton (`SingleTapeTM.isLBA_fence`, through
`SingleTapeTM.isLBA_of_stays_on_blank`). Informally, on `fenceInput w i j` it halts iff `tm`
halts on `w` without reading a cell at a wall position; this characterization is not formalized.
What is proved is its consequence: a halting run of `tm` reads finitely many cells, so `tm` halts
on `w` iff `fence tm` halts on `fenceInput w i j` for some `i` and `j`
(`SingleTapeTM.exists_haltsOn_fence_iff`). The proof relates the tapes of the two machines cell by
cell through the view `BiTape.toTape` of CSLib tapes as Mathlib tapes.

Applied to a single-tape recognizer `R` of the halting problem, this gives the code-free form of
Sipser's Theorem 5.10 (`SingleTapeTM.exists_isLBA_not_computablePred_forall_not_haltsOn`).
Sipser's `E_LBA` is a language of machine descriptions: the LBAs whose language is empty. For one
fixed machine, emptiness is a single bit. CSLib has no code type for machines, so here an LBA `F`
over the fenced alphabet is fixed (it is `fence R`), and its inputs are cut into slices, one for
each code `c` of a partial recursive function: the inputs `fenceInput (e c) i j` for all paddings
`i` and `j`, with a primitive recursive `e`. "`F` halts on no input of the slice of `c`" is
neither decidable nor recognizable in `c`. The slice does not depend on `F`, and the word `e c`
does not see the paddings, so `F` itself must run the computation within the space the paddings
give. Each slice is regular because of its shape, `wall lpad* (e c) pad* wall`. Informally, and
not proved here: with codes of machines, the LBA that checks that its input lies in the slice of
`c` and then runs `F` has empty language iff `F` halts on no input of the slice, so `E_LBA` is
undecidable by the same reduction. Sipser proves Theorem 5.10 differently, through computation
histories. The language of a machine here is the set of inputs on which it halts, the acceptance
convention of `SingleTapeRecognizable`.

## Main definitions

- `Cslib.Turing.SingleTapeTM.FenceSymbol`, `Cslib.Turing.SingleTapeTM.FenceState`: the alphabet
  and states of the fenced machine.
- `Cslib.Turing.SingleTapeTM.fence`: the fenced machine.
- `Cslib.Turing.SingleTapeTM.fenceInput`: a word with padding, between walls.

## Main results

- `Cslib.Turing.SingleTapeTM.getElem?_fenceInput`, `Cslib.Turing.SingleTapeTM.length_fenceInput`:
  the cells and the length of a fenced input.
- `Cslib.Turing.SingleTapeTM.isLBA_fence`: the fenced machine is a linear bounded automaton.
- `Cslib.Turing.SingleTapeTM.exists_haltsOn_fence_iff`: it halts on some padding of `w` iff `tm`
  halts on `w`.
- `Cslib.Turing.SingleTapeTM.exists_isLBA_not_computablePred_forall_not_haltsOn`: emptiness of a
  linear bounded automaton on the fenced input slices of a primitive recursive family of words is
  neither decidable nor recognizable (the code-free form of Sipser, Theorem 5.10).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.1:
  Theorem 5.10 (`E_LBA` is undecidable).
-/

@[expose] public section

set_option autoImplicit false

open Relation Computability Encodable MetaMathlibExt.TM2Recursive
open _root_.Turing

namespace Cslib.Turing.SingleTapeTM

/-- **Fenced alphabet.** For an alphabet $\Sigma$, the tape alphabet of the fenced machine consists
of a symbol for each letter of $\Sigma$, two kinds of padding cells (left and right), which the
simulated machine reads as blanks, and the wall, which marks the ends of the input. -/
inductive FenceSymbol (Symbol : Type) where
  /-- A symbol of the simulated machine. -/
  | sym (a : Symbol)
  /-- A padding cell to the right of the input, or a blank written by the simulated machine. -/
  | pad
  /-- A padding cell to the left of the input; the start phase steps over these cells. -/
  | lpad
  /-- An end marker. -/
  | wall
  deriving DecidableEq, Fintype

/-- **States of the fenced machine.** For a set of states $Q$, the states of the fenced machine are
two start states, a running state for each state $q \in Q$ of the simulated machine, and a trap
state. -/
inductive FenceState (State : Type) where
  /-- The initial state: on a wall, move right; on any other cell, enter the trap. -/
  | start₀
  /-- Step right over the left padding; on any other cell, act as `run` of the initial state of
  the simulated machine. -/
  | start₁
  /-- Run the simulated machine in state `q`; on a wall or a blank cell, enter the trap. -/
  | run (q : State)
  /-- The trap, entered on a wall or a blank cell: loop forever, leaving the tape unchanged. -/
  | trap
  deriving Fintype

section Input

variable {Symbol : Type}

/-- The fenced alphabet is inhabited by the padding cell `pad`. -/
instance : Inhabited (FenceSymbol Symbol) :=
  ⟨.pad⟩

/-- **Simulated cell of a fenced cell.** The simulated cell of a cell of the fenced machine is
the cell of the simulated machine that it stands for: a symbol of the simulated machine stands
for itself, and every other cell (a padding cell, a wall or a blank) stands for a blank. -/
def FenceSymbol.read : Option (FenceSymbol Symbol) → Option Symbol
  | some (.sym a) => some a
  | _ => none

/-- **Fenced cell of a write.** For a cell $o$ of the simulated machine, a symbol or a blank,
the fenced cell of $o$ is the cell the fenced machine writes for a write of $o$: $o$ itself if
$o$ is a symbol, and the padding cell $\mathrm{pad}$ if $o$ is a blank. -/
def FenceSymbol.ofCell : Option Symbol → FenceSymbol Symbol
  | some a => .sym a
  | none => .pad

/-- **Reading back a fenced cell of a write.** For every cell $o$ of the simulated machine, a
symbol or a blank, the simulated cell of the fenced cell of $o$ is $o$. -/
@[simp]
theorem FenceSymbol.read_ofCell (o : Option Symbol) : read (some (ofCell o)) = o := by
  cases o <;> rfl

/-- **Reading back a copied cell.** Let $o$ be a cell of the simulated machine, a symbol or a
blank, and copy it to the fenced machine, a symbol as itself and a blank as a blank. Then the
simulated cell of the copy is $o$. -/
@[simp]
theorem FenceSymbol.read_map_sym (o : Option Symbol) : read (o.map sym) = o := by
  cases o <;> rfl

/-- **A fenced cell of a write is never a wall.** For every cell $o$ of the simulated machine, a
symbol or a blank, the fenced cell of $o$ is not a wall. -/
theorem FenceSymbol.ofCell_ne_wall (o : Option Symbol) : ofCell o ≠ .wall := by
  cases o <;> simp [ofCell]

/-- **Fenced input.** For a word $w$ over an alphabet $\Sigma$ and $i, j \in \mathbb{N}$, the fenced
input of $w$ with $i$ padding cells on the left and $j$ on the right is the word over the fenced
alphabet of $\Sigma$ made of a wall, $i$ left padding cells, the letters of $w$ as symbols, $j$
right padding cells and a wall, in this order. -/
def fenceInput (w : List Symbol) (i j : ℕ) : List (FenceSymbol Symbol) :=
  .wall :: List.replicate i .lpad ++ w.map .sym ++ List.replicate j .pad ++ [.wall]

/-- **Cells of a fenced input.** Let $w$ be a word of length $\ell$ and $i, j, n \in \mathbb{N}$.
The cell at position $n$, counting from $0$, of the fenced input of $w$ with $i$ left and $j$
right padding cells is the wall if $n = 0$; a left padding cell if $1 \le n \le i$; the letter of
$w$ at position $n - i - 1$, also counting from $0$, as a symbol, if $i < n \le i + \ell$; a right
padding cell if $i + \ell < n \le i + \ell + j$; the wall if $n = i + \ell + j + 1$; and there is
no cell at a larger position $n$. -/
theorem getElem?_fenceInput (w : List Symbol) (i j n : ℕ) :
    (fenceInput w i j)[n]? =
      if n = 0 then some .wall
      else if n ≤ i then some .lpad
      else if n ≤ i + w.length then (w[n - (i + 1)]?).map .sym
      else if n ≤ i + w.length + j then some .pad
      else if n = i + w.length + j + 1 then some .wall
      else none := by
  rcases n with _ | n
  · rfl
  simp only [fenceInput, List.cons_append, List.getElem?_cons_succ, List.append_assoc,
    List.getElem?_append, List.length_replicate, List.length_map, List.getElem?_replicate,
    List.getElem?_map, List.getElem?_singleton]
  split_ifs <;> first | rfl | omega | contradiction | simp

/-- **Length of a fenced input.** For a word $w$ of length $n$ and natural numbers $i$ and $j$,
the fenced input of $w$ with $i$ padding cells on the left and $j$ on the right has length
$i + n + j + 2$: the word, the two paddings and the two walls. -/
@[simp]
theorem length_fenceInput (w : List Symbol) (i j : ℕ) :
    (fenceInput w i j).length = i + w.length + j + 2 := by
  simp [fenceInput]
  omega

end Input

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-- **A transition lifted to the fenced machine.** A transition of a single-tape machine $M$, made
of an optional symbol to write, an optional move and an optional next state, becomes the
transition of the fenced machine of $M$ that writes the symbol, or a right padding cell where $M$
writes a blank, makes the same move, and goes to the running state of the next state $q$ of $M$,
or halts where $M$ halts. -/
def fenceLift (r : Stmt Symbol × Option tm.State) :
    Stmt (FenceSymbol Symbol) × Option (FenceState tm.State) :=
  (⟨some (FenceSymbol.ofCell r.1.symbol), r.1.movement⟩, r.2.map .run)

/-- **The running transition of the fenced machine.** In the running state of a state $q$ of a
single-tape machine $M$, the fenced machine of $M$ acts on the cell under its head as follows: on a
symbol $a$ it makes the lifted transition of $M$ in state $q$ on $a$; on a left or right padding
cell it makes the lifted transition of $M$ in state $q$ on a blank; on a wall or a blank cell it
leaves the cell unchanged, does not move, and enters the trap. -/
def fenceRun (q : tm.State) (c : Option (FenceSymbol Symbol)) :
    Stmt (FenceSymbol Symbol) × Option (FenceState tm.State) :=
  match c with
  | some (.sym a) => tm.fenceLift (tm.tr q (some a))
  | some .pad | some .lpad => tm.fenceLift (tm.tr q none)
  | _ => (⟨c, none⟩, some .trap)

/-- **The fenced machine.** For a single-tape machine $M$ over a finite inhabited alphabet $\Sigma$,
the fenced machine of $M$ is the single-tape machine over the fenced alphabet of $\Sigma$ whose
states are the states of the fenced machine for the states of $M$, which starts in the first start
state and acts on the cell under its head as follows. In the first start state, on a wall it moves
right into the second start state, and on any other cell it leaves the cell unchanged, does not
move and enters the trap. In the second start state, on a left padding cell it moves right and
stays in that state, and on any other cell it makes the running transition of the initial state of
$M$. In the running state of a state $q$ of $M$ it makes the running transition of $q$. In the
trap it leaves the cell unchanged, does not move and stays in the trap.

So on the fenced input of a word $w$ it moves right off the left wall and over the left padding,
then runs $M$ from its initial state, and enters the trap when it reads a wall or a blank cell. On
a blank cell, in every state, it writes a blank and does not move. -/
abbrev fence : SingleTapeTM (FenceSymbol Symbol) where
  State := FenceState tm.State
  q₀ := .start₀
  tr
    | .start₀, c => match c with
      | some .wall => (⟨c, some .right⟩, some .start₁)
      | _ => (⟨c, none⟩, some .trap)
    | .start₁, c => match c with
      | some .lpad => (⟨c, some .right⟩, some .start₁)
      | _ => tm.fenceRun tm.q₀ c
    | .run q, c => tm.fenceRun q c
    | .trap, c => (⟨c, none⟩, some .trap)

/-- **The fenced machine is a linear bounded automaton.** For every single-tape Turing machine
$M$, the fenced machine of $M$ is a linear bounded automaton.

On a blank cell, in every state, the fenced machine writes a blank and does not move. -/
theorem isLBA_fence : (fence tm).IsLBA :=
  isLBA_of_stays_on_blank fun q ↦ by cases q <;> rfl

/-! ### The simulation -/

/-- The tape `T` of the fenced machine stands for the tape `t` of `tm`: each cell of `T` reads
(`FenceSymbol.read`) as the cell of `t` at the same position. -/
private def Sim (t : BiTape Symbol) (T : BiTape (FenceSymbol Symbol)) : Prop :=
  ∀ i, FenceSymbol.read (T.toTape.nth i) = t.toTape.nth i

/-- The cells of `T` within `r` cells of the head are symbols or padding cells. -/
private def Inside (r : ℕ) (T : BiTape (FenceSymbol Symbol)) : Prop :=
  ∀ i : ℤ, -r ≤ i → i ≤ r → T.toTape.nth i ≠ none ∧ T.toTape.nth i ≠ some .wall

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Writes and moves keep the simulation relation. -/
private theorem Sim.write_optionMove {t : BiTape Symbol} {T : BiTape (FenceSymbol Symbol)}
    (hs : Sim t T) (c : Option (FenceSymbol Symbol)) (d : Option Dir) :
    Sim ((t.write (FenceSymbol.read c)).optionMove d) ((T.write c).optionMove d) := by
  intro i
  rw [BiTape.nth_toTape_write_optionMove, BiTape.nth_toTape_write_optionMove]
  split_ifs
  · rfl
  · exact hs _

omit [Inhabited Symbol] [Fintype Symbol] in
/-- A write of a symbol or a padding cell, and a move, shrink the window `Inside` by one cell. -/
private theorem Inside.write_optionMove {r : ℕ} {T : BiTape (FenceSymbol Symbol)}
    (h : Inside (r + 1) T) {c : Option (FenceSymbol Symbol)} (hc : c ≠ none)
    (hc' : c ≠ some .wall) (d : Option Dir) : Inside r ((T.write c).optionMove d) := by
  intro i hi hi'
  have := BiTape.optionMoveOffset_bound d
  rw [BiTape.nth_toTape_write_optionMove]
  split_ifs
  · exact ⟨hc, hc'⟩
  · exact h _ (by push_cast; omega) (by push_cast; omega)

/-- One step of `tm` from the state `q` is one step of the fenced machine from `run q`, on a tape
standing for the tape of `tm`, with a symbol or a padding cell under the head. -/
private theorem fence_step_sim {q : tm.State} {t : BiTape Symbol} {T : BiTape (FenceSymbol Symbol)}
    (hs : Sim t T) (hT : T.head ≠ none) (hT' : T.head ≠ some .wall) :
    ∃ T', (fence tm).step ⟨some (.run q), T⟩ = some ⟨(tm.tr q t.head).2.map .run, T'⟩ ∧
      Sim ((t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement) T' ∧
      ∀ r : ℕ, Inside (r + 1) T → Inside r T' := by
  have hhead : FenceSymbol.read T.head = t.head := hs 0
  have htr : (fence tm).tr (.run q) T.head = tm.fenceLift (tm.tr q t.head) := by
    rw [← hhead]
    change tm.fenceRun q T.head = _
    rcases h : T.head with _ | (a | _ | _ | _)
    · exact absurd h hT
    · rfl
    · rfl
    · rfl
    · exact absurd h hT'
  refine ⟨(T.write (some (FenceSymbol.ofCell (tm.tr q t.head).1.symbol))).optionMove
    (tm.tr q t.head).1.movement, by rw [step_some, htr]; rfl, ?_,
    fun r h ↦ h.write_optionMove (Option.some_ne_none _) (by simp [FenceSymbol.ofCell_ne_wall]) _⟩
  simpa using hs.write_optionMove (some (FenceSymbol.ofCell (tm.tr q t.head).1.symbol))
    (tm.tr q t.head).1.movement

/-- From the trap, the fenced machine stays in the trap. -/
private theorem state_of_trap {T : BiTape (FenceSymbol Symbol)} {c : (fence tm).Cfg}
    (h : ReflTransGen (fence tm).TransitionRelation ⟨some .trap, T⟩ c) :
    c.state = some .trap := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rename_i b c' _
    obtain ⟨s, T'⟩ := b
    obtain rfl : s = some .trap := ih
    rw [TransitionRelation, step_some] at hstep
    obtain rfl := Option.some_injective _ hstep
    rfl

/-- **If the fenced machine halts from `run q`, then `tm` halts from `q`**, on tapes in the
simulation relation: until it halts, the fenced machine either simulates a step of `tm` or is in
the trap. -/
private theorem haltsFrom_of_haltsFrom_fence {a : (fence tm).Cfg} (h : (fence tm).HaltsFrom a) :
    ∀ {q : tm.State} {t : BiTape Symbol} {T : BiTape (FenceSymbol Symbol)},
      a = ⟨some (.run q), T⟩ → Sim t T → tm.HaltsFrom ⟨some q, t⟩ := by
  obtain ⟨b, hab, hb⟩ := h
  induction hab using ReflTransGen.head_induction_on with
  | refl =>
    rintro q t T rfl -
    cases hb
  | head hac hcb ih =>
    rename_i c
    rintro q t T rfl hs
    by_cases hT : T.head = none ∨ T.head = some .wall
    · have htr : c.state = some .trap := by
        rw [TransitionRelation, step_some] at hac
        rw [← Option.some_injective _ hac]
        change (tm.fenceRun q T.head).2 = _
        rcases hT with hT | hT <;> rw [hT] <;> rfl
      obtain ⟨s, T''⟩ := c
      obtain rfl : s = some .trap := htr
      have := state_of_trap tm hcb
      rw [hb] at this
      cases this
    · push Not at hT
      obtain ⟨T', hstep, hs', -⟩ := fence_step_sim tm (q := q) hs hT.1 hT.2
      rw [TransitionRelation, hstep] at hac
      obtain rfl := Option.some_injective _ hac
      have htm : tm.TransitionRelation ⟨some q, t⟩ ⟨(tm.tr q t.head).2,
          (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩ :=
        step_some tm q t
      revert htm ih
      generalize (tm.tr q t.head).2 = q'
      rintro ih htm
      cases q' with
      | none => exact ⟨_, .single htm, rfl⟩
      | some q' => exact (haltsFrom_iff_of_reflTransGen (.single htm)).mpr (ih rfl hs')

/-- **A run of `tm` of `n ≤ K` steps is a run of the fenced machine**, from a tape standing for
the tape of `tm` with symbols or padding cells within `K` cells of the head. -/
private theorem reflTransGen_fence {t₀ : BiTape Symbol} {T₀ : BiTape (FenceSymbol Symbol)} {K : ℕ}
    (hs : Sim t₀ T₀) (hI : Inside K T₀) {c : tm.Cfg} {n : ℕ}
    (h : RelatesInSteps tm.TransitionRelation ⟨some tm.q₀, t₀⟩ c n) (hn : n ≤ K) :
    ∃ T, Sim c.BiTape T ∧ Inside (K - n) T ∧
      ReflTransGen (fence tm).TransitionRelation ⟨some (.run tm.q₀), T₀⟩ ⟨c.state.map .run, T⟩ := by
  induction h with
  | refl => exact ⟨T₀, hs, by simpa using hI, .refl⟩
  | tail b c' n _ hstep ih =>
    obtain ⟨T, hsT, hIT, hrun⟩ := ih (by omega)
    obtain ⟨_ | q, tb⟩ := b
    · cases hstep
    obtain ⟨h0, h0'⟩ := hIT 0 (by omega) (by omega)
    obtain ⟨T', hfs, hs', hI'⟩ := fence_step_sim tm (q := q) hsT h0 h0'
    rw [TransitionRelation, step_some] at hstep
    obtain rfl := Option.some_injective _ hstep
    refine ⟨T', hs', hI' _ (by rwa [show K - n = K - (n + 1) + 1 by omega] at hIT), ?_⟩
    exact hrun.tail hfs

/-! ### The start phase -/

/-- The tape of the fenced machine after the start phase on `fenceInput w i j`, with the head on
the first cell after the left padding. -/
private def startTape (w : List Symbol) (i j : ℕ) : BiTape (FenceSymbol Symbol) :=
  BiTape.moveRight^[i + 1] (BiTape.mk₁ (fenceInput w i j))

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The cells of `startTape w i j`. -/
private theorem nth_startTape (w : List Symbol) (i j : ℕ) (z : ℤ) :
    (startTape w i j).toTape.nth z =
      if 0 ≤ z + (i + 1) then (fenceInput w i j)[(z + (i + 1)).toNat]? else none := by
  rw [startTape, BiTape.nth_toTape_moveRight_iterate, BiTape.nth_toTape_mk₁]
  push_cast
  rfl

/-- The start phase: the fenced machine moves right off the left wall and over the left
padding. -/
private theorem reflTransGen_start (w : List Symbol) (i j : ℕ) :
    ReflTransGen (fence tm).TransitionRelation ((fence tm).initCfg (fenceInput w i j))
      ⟨some .start₁, startTape w i j⟩ := by
  have key : ∀ m ≤ i, ReflTransGen (fence tm).TransitionRelation
      ((fence tm).initCfg (fenceInput w i j))
      ⟨some .start₁, BiTape.moveRight^[m + 1] (BiTape.mk₁ (fenceInput w i j))⟩ := by
    intro m hm
    induction m with
    | zero => exact .single rfl
    | succ m ih =>
      refine (ih (by omega)).tail ?_
      have hhead : (BiTape.moveRight^[m + 1] (BiTape.mk₁ (fenceInput w i j))).head =
          some .lpad := by
        have h := BiTape.nth_toTape_moveRight_iterate (BiTape.mk₁ (fenceInput w i j)) (m + 1) 0
        change (BiTape.moveRight^[m + 1] (BiTape.mk₁ (fenceInput w i j))).head = _ at h
        rw [h, BiTape.nth_toTape_mk₁, zero_add, ite_eq_left (by omega), Int.toNat_natCast,
          getElem?_fenceInput]
        split_ifs <;> first | rfl | omega | contradiction
      rw [TransitionRelation, step_some, hhead, Function.iterate_succ_apply' _ (m + 1)]
      generalize BiTape.moveRight^[m + 1] (BiTape.mk₁ (fenceInput w i j)) = T at hhead ⊢
      obtain ⟨h, L, R⟩ := T
      cases hhead
      rfl
  exact key i le_rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- After the start phase, the cell under the head is not left padding. -/
private theorem head_startTape_ne (w : List Symbol) (i j : ℕ) :
    (startTape w i j).head ≠ some .lpad := by
  have := nth_startTape w i j 0
  rw [show (startTape w i j).toTape.nth 0 = (startTape w i j).head from rfl] at this
  rw [this, ite_eq_left (by omega), show ((0 : ℤ) + (i + 1)).toNat = i + 1 by omega,
    getElem?_fenceInput]
  split_ifs <;> first | omega | simp

omit [Inhabited Symbol] [Fintype Symbol] in
/-- After the start phase, the tape stands for the input tape of `w`. -/
private theorem sim_startTape (w : List Symbol) (i j : ℕ) :
    Sim (BiTape.mk₁ w) (startTape w i j) := by
  intro z
  rw [nth_startTape, BiTape.nth_toTape_mk₁]
  by_cases h1 : 0 ≤ z + (i + 1)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, z + (i + 1) = n := ⟨_, (Int.toNat_of_nonneg h1).symm⟩
    rw [ite_eq_left h1]
    simp only [hn, Int.toNat_natCast, getElem?_fenceInput]
    by_cases h2 : 0 ≤ z
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, z = m := ⟨_, (Int.toNat_of_nonneg h2).symm⟩
      obtain rfl : n = m + (i + 1) := by omega
      simp only [h2, ↓reduceIte, Int.toNat_natCast, Nat.add_sub_cancel]
      split_ifs <;>
        first | omega | contradiction | exact FenceSymbol.read_map_sym _ |
          (simp [FenceSymbol.read]; omega)
    · simp only [h2, ↓reduceIte]
      split_ifs <;> first | omega | rfl
  · simp only [h1, ↓reduceIte]
    split_ifs <;> first | omega | rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- After the start phase on `fenceInput w (K + 1) (K + 1)`, the cells within `K` cells of the
head are symbols or padding cells. -/
private theorem inside_startTape (w : List Symbol) (K : ℕ) :
    Inside K (startTape w (K + 1) (K + 1)) := by
  intro z hz hz'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z + ((K + 1 : ℕ) + 1) = n :=
    ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [nth_startTape, ite_eq_left (by omega), hn, Int.toNat_natCast, getElem?_fenceInput]
  split_ifs <;> first | omega | (simp; done) | (simp; omega)

/-- In the state `start₁` on a cell that is not left padding, the fenced machine acts as in
`run tm.q₀`. -/
private theorem step_start₁ {T : BiTape (FenceSymbol Symbol)} (h : T.head ≠ some .lpad) :
    (fence tm).step ⟨some .start₁, T⟩ = (fence tm).step ⟨some (.run tm.q₀), T⟩ := by
  have : (fence tm).tr .start₁ T.head = (fence tm).tr (.run tm.q₀) T.head := by
    rcases hT : T.head with _ | (_ | _ | _ | _)
    · rfl
    · rfl
    · rfl
    · exact absurd hT h
    · rfl
  rw [step_some, step_some, this]

/-- The fenced machine halts on `fenceInput w i j` iff it halts from `run tm.q₀` after the start
phase. -/
private theorem haltsOn_fence_iff (w : List Symbol) (i j : ℕ) :
    (fence tm).HaltsOn (fenceInput w i j) ↔
      (fence tm).HaltsFrom ⟨some (.run tm.q₀), startTape w i j⟩ := by
  rw [haltsOn_iff_haltsFrom, haltsFrom_iff_of_reflTransGen (reflTransGen_start tm w i j),
    haltsFrom_iff_of_step_eq (step_start₁ tm (head_startTape_ne w i j))]

/-! ### Correctness -/

/-- **The fenced machine halts on some padding of a word iff the machine halts on it.** Let $M$ be
a single-tape machine over a finite inhabited alphabet and $w$ a word over that alphabet. The
fenced machine of $M$ halts on the fenced input of $w$ with $i$ padding cells on the left and $j$
on the right for some $i, j \in \mathbb{N}$ if and only if $M$ halts on $w$.

A halting run of $M$ of $n$ steps stays within $n$ cells of its start, so it runs unchanged inside
the walls of the fenced input of $w$ with $n + 1$ padding cells on each side; conversely, the
fenced machine halts only by simulating a halting run of $M$. -/
theorem exists_haltsOn_fence_iff (w : List Symbol) :
    (∃ i j, (fence tm).HaltsOn (fenceInput w i j)) ↔ tm.HaltsOn w := by
  constructor
  · rintro ⟨i, j, h⟩
    exact haltsFrom_of_haltsFrom_fence tm ((haltsOn_fence_iff tm w i j).1 h) rfl
      (sim_startTape w i j)
  · rintro ⟨c, hc, hstate⟩
    obtain ⟨n, hn⟩ := hc.relatesInSteps
    obtain ⟨T, -, -, hrun⟩ :=
      reflTransGen_fence tm (sim_startTape w (n + 1) (n + 1)) (inside_startTape w n) hn le_rfl
    refine ⟨n + 1, n + 1, (haltsOn_fence_iff tm w (n + 1) (n + 1)).2 ⟨_, hrun, ?_⟩⟩
    simp [hstate]

/-- **The fenced machine halts on no padding of a word iff the machine does not halt on it.** Let
$M$ be a single-tape machine over a finite inhabited alphabet and $w$ a word over that alphabet.
The fenced machine of $M$ halts on none of the fenced inputs of $w$, with $i$ padding cells on the
left and $j$ on the right for $i, j \in \mathbb{N}$, if and only if $M$ does not halt on $w$. -/
theorem forall_not_haltsOn_fence_iff (w : List Symbol) :
    (∀ i j, ¬(fence tm).HaltsOn (fenceInput w i j)) ↔ ¬tm.HaltsOn w := by
  rw [← exists_haltsOn_fence_iff]
  simp

/-! ### Emptiness of an LBA on computable input slices is undecidable -/

/-- **Emptiness of a linear bounded automaton on computable input slices is undecidable.** There
exist a finite inhabited alphabet $\Gamma$ with a primitive recursive encoding, a linear bounded
automaton $F$ over the fenced alphabet of $\Gamma$, and a primitive recursive map $e$ from codes of
partial recursive functions to words over $\Gamma$, such that the set of codes $c$ for which $F$
halts on none of the fenced inputs of $e(c)$, with $i$ padding cells on the left and $j$ on the
right for any $i, j \in \mathbb{N}$, is neither computable nor recursively enumerable.

This is the code-free form of Sipser, Theorem 5.10. Take for $F$ the fenced machine of a
single-tape recognizer $R$ of the set of codes that halt on input $0$, and for $e(c)$ the input of
$c$ to $R$: then $F$ halts on no fenced input of $e(c)$ iff $c$ does not halt on $0$. The word
$e(c)$ does not see the paddings $i$ and $j$, so $F$ itself runs the computation within the space
they give.

Sipser's $E_{\mathrm{LBA}}$ is a language of machine descriptions, the LBAs with empty language;
without a type of codes for machines, this is the form available. Each slice, the set of fenced
inputs of $e(c)$ over all paddings, is regular because of its shape: a wall, any number of left
padding cells, the word $e(c)$, any number of right padding cells and a wall. Informally, and not
proved here: with codes of machines, the LBA that checks that its input lies in the slice of $c$
and then runs $F$ has empty language iff $F$ halts on no input of the slice, and
$E_{\mathrm{LBA}}$ is undecidable by the same reduction. -/
theorem exists_isLBA_not_computablePred_forall_not_haltsOn :
    ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ) (_ : Primcodable Γ)
      (F : SingleTapeTM (FenceSymbol Γ)) (e : Nat.Partrec.Code → List Γ), F.IsLBA ∧ Primrec e ∧
      ¬ComputablePred (fun c ↦ ∀ i j, ¬F.HaltsOn (fenceInput (e c) i j)) ∧
      ¬REPred (fun c ↦ ∀ i j, ¬F.HaltsOn (fenceInput (e c) i j)) := by
  obtain ⟨Γ, _, _, ι, -, R, hR⟩ := Decidability.singleTapeRecognizable_halting 0
  classical
  let _ : Primcodable Γ := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have he : (fun c : Nat.Partrec.Code ↦ ∀ i j,
      ¬(fence R).HaltsOn (fenceInput ((encodeNat (encode c)).map ι) i j)) =
      fun c ↦ ¬(c.eval 0).Dom :=
    funext fun c ↦ propext <| (forall_not_haltsOn_fence_iff R _).trans (not_congr (hR c))
  refine ⟨Γ, inferInstance, inferInstance, inferInstance, fence R,
    fun c ↦ (encodeNat (encode c)).map ι, isLBA_fence R,
    Primrec.list_map (primrec_encodeNat.comp Primrec.encode)
      ((Primrec.dom_finite ι).comp Primrec.snd).to₂, ?_, ?_⟩
  · rw [he]
    exact fun h ↦ ComputablePred.halting_problem 0 (by simpa using h.not)
  · rw [he]
    exact ComputablePred.halting_problem_not_re 0

end Cslib.Turing.SingleTapeTM
