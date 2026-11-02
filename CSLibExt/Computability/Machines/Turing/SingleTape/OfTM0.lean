/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Classes
public import CSLibExt.Computability.Machines.Turing.SingleTape.TapeView
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Logic.Equiv.Option

/-!
# Mathlib's `TM0` machines as CSLib single-tape machines

Mathlib's Post-Turing machines `Turing.TM0.Machine Γ₀ Λ` read and write symbols of `Γ₀`, with
`default : Γ₀` as the blank, and may have infinitely many states, of which a finite set `S`
supports the machine (`Turing.TM0.Supports`). CSLib's single-tape machines
`Cslib.Turing.SingleTapeTM Symbol` have finitely many states, and their tape cells hold
`Option Symbol`, with `none` as the blank. This file runs the first kind on the second, step for
step.

The simulating machine `SingleTapeTM.ofTM0 M S hS` writes the non-blank symbols
`NonBlank Γ₀ = {x : Γ₀ // x ≠ default}`, so that a cell `Option (NonBlank Γ₀)` is a `Γ₀` symbol
through `Equiv.optionSubtypeNe`, with `none` for the blank. Its states are the elements of `S`.
Each `TM0` step is one step of the simulating machine; where the `TM0` machine halts, the
simulating machine takes one more step into its halting state and leaves the tape unchanged.
Tapes correspond cell by cell through `SingleTapeTM.toTape`: the view `BiTape.toTape` of
`TapeView`, a tape of cells, mapped to `Γ₀` by the pointed map `Equiv.optionSubtypeNe default`
(`SingleTapeTM.cellSymbol`). It is injective because a `StackTape` does not end in a blank.
Restricting the states to the support `S` is the same idea as
`MetaMathlibExt.TM0Restrict.restrict` (a `TM0` machine on the subtype `S`), done here directly in
the transition function of the simulating machine.

## Main results

- `Cslib.Turing.SingleTapeTM.ofTM0`: the simulating machine.
- `Cslib.Turing.SingleTapeTM.haltsOn_ofTM0_iff`: it halts on `l` exactly when the `TM0`
  machine halts on `l`.
- `Cslib.Turing.SingleTapeTM.outputs_ofTM0`: when the `TM0` machine halts on `l` with the tape
  `Tape.mk₁ l'`, the simulating machine outputs `l'`.
- `Cslib.Turing.SingleTapeTM.outputsWithinTime_ofTM0`: it does so within one step more than the
  `TM0` run.
-/

@[expose] public section

set_option autoImplicit false

open Relation StateTransition
open _root_.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Γ₀ Λ : Type} [Inhabited Γ₀] [Inhabited Λ]

/-- **Non-blank symbols.** For an alphabet $\Gamma_0$ with a distinguished blank symbol $b$, the
non-blank symbols of $\Gamma_0$ are the elements $x \in \Gamma_0$ with $x \ne b$. They form the
tape alphabet of the single-tape machine that simulates a Post–Turing machine over $\Gamma_0$. -/
abbrev NonBlank (Γ₀ : Type) [Inhabited Γ₀] : Type := {x : Γ₀ // x ≠ default}

section Tape

variable [DecidableEq Γ₀]

/-- **Cell symbol.** Let $\Gamma_0$ be an alphabet with blank symbol $b$. A tape cell over the
non-blank symbols of $\Gamma_0$ is either blank or holds a symbol $x \ne b$ of $\Gamma_0$. Its cell
symbol is $b$ for the blank cell and $x$ for the cell holding $x$. This map from cells to
$\Gamma_0$ sends the blank cell to the blank symbol, so it is a pointed map. -/
def cellSymbol : PointedMap (Option (NonBlank Γ₀)) Γ₀ :=
  ⟨Equiv.optionSubtypeNe default, rfl⟩

/-- **Value of the cell-symbol map.** For every cell $o$ over the non-blank symbols of an alphabet
$\Gamma_0$ with blank symbol $b$, the cell symbol of $o$ is $b$ when $o$ is the blank cell and is
$x$ when $o$ holds the non-blank symbol $x$. -/
@[simp]
theorem cellSymbol_apply (o : Option (NonBlank Γ₀)) :
    cellSymbol o = Equiv.optionSubtypeNe default o :=
  rfl

/-- **The cell-symbol map is injective.** Distinct cells over the non-blank symbols of an alphabet
$\Gamma_0$ have distinct cell symbols in $\Gamma_0$. -/
theorem cellSymbol_injective : Function.Injective (cellSymbol (Γ₀ := Γ₀)) :=
  (Equiv.optionSubtypeNe default).injective

/-- **Half-tape of a stack tape of non-blank symbols.** Let $\Gamma_0$ be an alphabet with blank
symbol $b$ and $N = \Gamma_0 \setminus \{b\}$ its non-blank symbols. A stack tape $s$ over $N$, a
finite list of cells each blank or holding a symbol of $N$ and not ending in a blank cell, is read
as the TM0 half-tape over $\Gamma_0$ whose $i$-th symbol is that of the $i$-th cell of $s$: $b$
for a blank cell, $x$ for a cell holding $x$, and $b$ past the end of $s$. -/
def toListBlank (s : StackTape (NonBlank Γ₀)) : ListBlank Γ₀ :=
  s.toListBlank.map cellSymbol

/-- **Post–Turing reading of a tape over the non-blank symbols.** Let $\Gamma_0$ be an alphabet
whose default symbol is the blank. The Post–Turing reading of a two-way tape $t$ whose cells are
blank or hold non-blank symbols of $\Gamma_0$ is the Post–Turing machine tape over $\Gamma_0$
obtained cell by cell: take the view of $t$ as a tape of cells, each cell at its position relative
to the head and blank cells past the ends, and replace each cell by its symbol, a non-blank symbol
$x$ by $x$ itself and the blank cell by the blank of $\Gamma_0$. -/
def toTape (t : BiTape (NonBlank Γ₀)) : Tape Γ₀ :=
  t.toTape.map cellSymbol

/-- **The empty stack tape reads as the blank half-tape.** For an alphabet $\Gamma_0$ with blank
symbol $b$, the empty stack tape over the non-blank symbols of $\Gamma_0$ reads as the half-tape
of the empty list, all of whose symbols are $b$. -/
@[simp]
theorem toListBlank_nil : toListBlank (StackTape.nil : StackTape (NonBlank Γ₀)) = ListBlank.mk [] :=
  rfl

/-- **Pushing a cell onto a stack tape of non-blank symbols.** Let $\Gamma_0$ be an alphabet with
blank symbol $b$ and $N = \Gamma_0 \setminus \{b\}$. Read a cell over $N$ as a symbol of
$\Gamma_0$: $b$ for the blank cell, $x$ for a cell holding $x$. For every cell $o$ and every stack
tape $s$ over $N$, the half-tape read from the stack tape obtained by pushing $o$ onto $s$ is the
half-tape read from $s$ with the symbol of $o$ pushed onto its front.

For the blank cell this holds because the half-tape is blank beyond its end. -/
@[simp]
theorem toListBlank_cons (o : Option (NonBlank Γ₀)) (s : StackTape (NonBlank Γ₀)) :
    toListBlank (StackTape.cons o s) =
      (toListBlank s).cons (Equiv.optionSubtypeNe default o) := by
  simp [toListBlank, ListBlank.map_cons]

/-- **First symbol of a half-tape read from non-blank cells.** Let $\Gamma_0$ be an alphabet with
blank symbol $b$. For every stack tape $s$ of cells over the non-blank symbols of $\Gamma_0$ (a
finite list of cells, blank beyond its end), the first symbol of the half-tape over $\Gamma_0$
read from $s$ is the cell symbol of the first cell of $s$; when $s$ is empty this is $b$. -/
@[simp]
theorem head_toListBlank (s : StackTape (NonBlank Γ₀)) :
    (toListBlank s).head = Equiv.optionSubtypeNe default s.head := by
  simp [toListBlank, ListBlank.head_map]

/-- **Dropping the first cell of a stack tape of non-blank symbols.** For an alphabet $\Gamma_0$
with blank symbol $b$ and every stack tape $s$ over the non-blank symbols of $\Gamma_0$, dropping
the first symbol of the half-tape read from $s$ gives the half-tape read from $s$ with its first
cell removed (the empty stack tape staying empty). -/
@[simp]
theorem tail_toListBlank (s : StackTape (NonBlank Γ₀)) :
    (toListBlank s).tail = toListBlank s.tail := by
  simp [toListBlank, ListBlank.tail_map]

/-- **A word of non-blank symbols reads as itself.** For an alphabet $\Gamma_0$ with blank symbol
$b$ and a word $w$ of non-blank symbols of $\Gamma_0$, the half-tape read from the stack tape whose
cells hold the letters of $w$ in order is the half-tape of $w$, viewed as a word over $\Gamma_0$. -/
@[simp]
theorem toListBlank_mapSome (l : List (NonBlank Γ₀)) :
    toListBlank (StackTape.mapSome l) = ListBlank.mk (l.map Subtype.val) := by
  simp [toListBlank, ListBlank.map_mk, Function.comp_def]

/-- A pointed map that is injective on symbols is injective on half-tapes. Generic; it could
become `Turing.ListBlank.map_injective` (with `Turing.Tape.map_injective`) in MathlibExt. -/
private theorem listBlank_map_injective {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    {f : PointedMap Γ Γ'} (hf : Function.Injective f) : Function.Injective (ListBlank.map f) :=
  fun _ _ h ↦ ListBlank.ext fun i ↦ hf (by rw [← ListBlank.nth_map, ← ListBlank.nth_map, h])

/-- **Distinct stack tapes of non-blank symbols read as distinct half-tapes.** For an alphabet
$\Gamma_0$ with blank symbol $b$, two stack tapes over the non-blank symbols of $\Gamma_0$ that read
as the same half-tape over $\Gamma_0$ are equal.

A stack tape does not end in a blank, so the trailing blanks of a half-tape do not come from
cells. -/
theorem toListBlank_injective : Function.Injective (toListBlank (Γ₀ := Γ₀)) :=
  (listBlank_map_injective cellSymbol_injective).comp StackTape.toListBlank_injective

/-- **Head symbol of a tape read from non-blank cells.** For every two-way tape $t$ of cells over
the non-blank symbols of an alphabet $\Gamma_0$, the symbol under the head of the tape over
$\Gamma_0$ read from $t$ is the cell symbol of the cell under the head of $t$. -/
@[simp]
theorem head_toTape (t : BiTape (NonBlank Γ₀)) :
    (toTape t).head = Equiv.optionSubtypeNe default t.head :=
  rfl

/-- **Writing commutes with the Post–Turing reading of a tape.** Let $\Gamma_0$ be an alphabet
whose default symbol is the blank, and for a two-way tape $t$ whose cells are blank or hold
non-blank symbols of $\Gamma_0$, let $\tau(t)$ be the Post–Turing reading of $t$, a Post–Turing
machine tape over $\Gamma_0$. For every such $t$ and every cell $o$, blank or holding a non-blank
symbol, $\tau$ of $t$ with $o$ written under the head is $\tau(t)$ with the symbol of $o$ written
under the head, where the symbol of $o$ is $x$ if $o$ holds $x$ and the blank of $\Gamma_0$ if $o$
is blank. -/
@[simp]
theorem toTape_write (t : BiTape (NonBlank Γ₀)) (o : Option (NonBlank Γ₀)) :
    toTape (t.write o) = (toTape t).write (Equiv.optionSubtypeNe default o) := by
  rw [toTape, BiTape.toTape_write, Tape.map_write, cellSymbol_apply, toTape]

/-- **Head moves commute with the Post–Turing reading of a tape.** Let $\Gamma_0$ be an alphabet
whose default symbol is the blank, and for a two-way tape $t$ whose cells are blank or hold
non-blank symbols of $\Gamma_0$, let $\tau(t)$ be the Post–Turing reading of $t$, a Post–Turing
machine tape over $\Gamma_0$. For every such $t$ and every direction $d$, left or right, $\tau$ of
$t$ with its head moved in direction $d$ is $\tau(t)$ with its head moved in direction $d$. -/
@[simp]
theorem toTape_move (t : BiTape (NonBlank Γ₀)) (d : Dir) :
    toTape (t.move d) = (toTape t).move d := by
  rw [toTape, BiTape.toTape_move, Tape.map_move, toTape]

/-- **Optional head moves commute with the Post–Turing reading of a tape.** Let $\Gamma_0$ be an
alphabet whose default symbol is the blank, and for a two-way tape $t$ whose cells are blank or
hold non-blank symbols of $\Gamma_0$, let $\tau(t)$ be the Post–Turing reading of $t$, a
Post–Turing machine tape over $\Gamma_0$. For every such $t$ and every optional move $d$, which is
either no move or a direction, $\tau$ of $t$ after the optional move $d$ is $\tau(t)$ when $d$ is
no move, and $\tau(t)$ with its head moved in direction $d$ when $d$ is a direction. -/
theorem toTape_optionMove (t : BiTape (NonBlank Γ₀)) (d : Option Dir) :
    toTape (t.optionMove d) = d.elim (toTape t) fun d ↦ (toTape t).move d := by
  cases d <;> simp [BiTape.optionMove]

/-- **The Post–Turing reading of an input tape.** Let $\Gamma_0$ be an alphabet whose default
symbol is the blank. For every word $l$ of non-blank symbols of $\Gamma_0$, the Post–Turing
reading of the two-way input tape of $l$ (the head on the first symbol of $l$, the rest of $l$ to
its right, every other cell blank) is the Post–Turing machine input tape of $l$ read as a word
over $\Gamma_0$, with the head on the first symbol of $l$ and the rest of $l$ to its right. -/
@[simp]
theorem toTape_mk₁ (l : List (NonBlank Γ₀)) :
    toTape (BiTape.mk₁ l) = Tape.mk₁ (l.map Subtype.val) := by
  simp [toTape, Tape.map_mk₁, Function.comp_def]

/-- **Distinct tapes of non-blank symbols read as distinct TM0 tapes.** For an alphabet
$\Gamma_0$ with blank symbol $b$, two tapes over the non-blank symbols of $\Gamma_0$ that read,
cell by cell, as the same TM0 tape over $\Gamma_0$ are equal. -/
theorem toTape_injective : Function.Injective (toTape (Γ₀ := Γ₀)) := by
  refine Function.Injective.comp (fun T₁ T₂ h ↦ ?_) BiTape.toTape_injective
  obtain ⟨a₁, L₁, R₁⟩ := T₁
  obtain ⟨a₂, L₂, R₂⟩ := T₂
  simp only [Tape.map, Tape.mk.injEq] at h
  obtain ⟨ha, hL, hR⟩ := h
  rw [cellSymbol_injective ha, listBlank_map_injective cellSymbol_injective hL,
    listBlank_map_injective cellSymbol_injective hR]

end Tape

variable [Fintype Γ₀] [DecidableEq Γ₀] [Inhabited (NonBlank Γ₀)]
variable (M : TM0.Machine Γ₀ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S)

/-- **Single-tape simulation of a Post–Turing machine.** Let $\Gamma_0$ be a finite alphabet with
blank symbol $b$ and at least one non-blank symbol, and let $M$ be a Post–Turing machine over
$\Gamma_0$ with start state $q_0$, supported by the finite set of states $S$ (so $q_0 \in S$, and
from a state in $S$ the machine $M$ only enters states in $S$). The single-tape machine simulating
$M$ has the non-blank symbols of $\Gamma_0$ as tape alphabet, $S$ as set of states and $q_0$ as
start state. In a state $q$, reading a cell $s$ whose cell symbol is $a$, it acts as follows. If
$M$ halts in $q$ on $a$, it writes $s$ back and halts. If $M$ moves the head in direction $d$ and
enters $q'$, it writes $s$ back, moves in direction $d$ and enters $q'$. If $M$ writes $a'$ and
enters $q'$, it writes the blank cell when $a' = b$ and otherwise the cell holding $a'$, does not
move, and enters $q'$.

CSLib machines need a chosen symbol of their alphabet, so an alphabet whose only symbol is the
blank is excluded. -/
def ofTM0 : SingleTapeTM (NonBlank Γ₀) where
  State := {q // q ∈ S}
  q₀ := ⟨default, hS.1⟩
  tr q s :=
    match h : M q.1 (Equiv.optionSubtypeNe default s) with
    | none => (⟨s, none⟩, none)
    | some (q', .move d) => (⟨s, some d⟩, some ⟨q', hS.2 h q.2⟩)
    | some (q', .write a) =>
      (⟨(Equiv.optionSubtypeNe default).symm a, none⟩, some ⟨q', hS.2 h q.2⟩)

/-- Where `M` halts on the symbol of the cell `s`, `ofTM0 M S hS` writes `s` back and halts. -/
private theorem ofTM0_tr_of_eq_none {q : Λ} (hq : q ∈ S) {s : Option (NonBlank Γ₀)}
    (h : M q (Equiv.optionSubtypeNe default s) = none) :
    (ofTM0 M S hS).tr ⟨q, hq⟩ s = (⟨s, none⟩, none) := by
  simp only [ofTM0]
  split <;> rename_i heq <;> rw [heq] at h <;> cases h

/-- Where `M` moves, `ofTM0 M S hS` writes the cell back and moves. -/
private theorem ofTM0_tr_of_eq_move {q q' : Λ} (hq : q ∈ S) {s : Option (NonBlank Γ₀)} {d : Dir}
    (h : M q (Equiv.optionSubtypeNe default s) = some (q', .move d)) :
    (ofTM0 M S hS).tr ⟨q, hq⟩ s = (⟨s, some d⟩, some ⟨q', hS.2 h hq⟩) := by
  simp only [ofTM0]
  split <;> rename_i heq <;> rw [heq] at h <;> cases h
  rfl

/-- Where `M` writes `a`, `ofTM0 M S hS` writes the cell of `a`. -/
private theorem ofTM0_tr_of_eq_write {q q' : Λ} (hq : q ∈ S) {s : Option (NonBlank Γ₀)} {a : Γ₀}
    (h : M q (Equiv.optionSubtypeNe default s) = some (q', .write a)) :
    (ofTM0 M S hS).tr ⟨q, hq⟩ s =
      (⟨(Equiv.optionSubtypeNe default).symm a, none⟩, some ⟨q', hS.2 h hq⟩) := by
  simp only [ofTM0]
  split <;> rename_i heq <;> rw [heq] at h <;> cases h
  rfl

/-- **The simulation halts one step after the TM0 machine.** Let $M$ be a TM0 machine over a
finite alphabet $\Gamma_0$ with blank symbol $b$ and at least one non-blank symbol, supported by a
finite set $S$ of states, and let $\widehat{M}$ be the single-tape machine over the non-blank
symbols $N = \Gamma_0 \setminus \{b\}$ simulating $M$. For a tape $t$ over $N$, write $\tau(t)$
for the TM0 tape read from $t$ cell by cell. If $q \in S$ and $M$ has no step from the
configuration $(q, \tau(t))$, then one step of $\widehat{M}$ from the configuration $(q, t)$
leads to its halting state with the tape $t$ unchanged. -/
theorem step_ofTM0_of_step_eq_none {q : Λ} (hq : q ∈ S) {t : BiTape (NonBlank Γ₀)}
    (h : TM0.step M ⟨q, toTape t⟩ = none) :
    (ofTM0 M S hS).step ⟨some ⟨q, hq⟩, t⟩ = some ⟨none, t⟩ := by
  have hM : M q (Equiv.optionSubtypeNe default t.head) = none := by
    simpa [TM0.step] using h
  simp only [step, ofTM0_tr_of_eq_none M S hS hq hM]
  rfl

/-- **Each TM0 step is one step of the simulation.** Let $M$ be a TM0 machine over a finite
alphabet $\Gamma_0$ with blank symbol $b$ and at least one non-blank symbol, supported by a finite
set $S$ of states, and let $\widehat{M}$ be the single-tape machine over the non-blank symbols
$N = \Gamma_0 \setminus \{b\}$ simulating $M$. For a tape $t$ over $N$, write $\tau(t)$ for the
TM0 tape read from $t$ cell by cell. If $q \in S$ and one step of $M$ takes the configuration
$(q, \tau(t))$ to a configuration $(q', T')$, then $q' \in S$ and there is a tape $t'$ over $N$
with $\tau(t') = T'$ such that one step of $\widehat{M}$ takes the configuration $(q, t)$ to the
configuration $(q', t')$. -/
theorem step_ofTM0_of_step_eq_some {q : Λ} (hq : q ∈ S) {t : BiTape (NonBlank Γ₀)}
    {c : TM0.Cfg Γ₀ Λ} (h : TM0.step M ⟨q, toTape t⟩ = some c) :
    ∃ (hc : c.q ∈ S) (t' : BiTape (NonBlank Γ₀)), toTape t' = c.Tape ∧
      (ofTM0 M S hS).step ⟨some ⟨q, hq⟩, t⟩ = some ⟨some ⟨c.q, hc⟩, t'⟩ := by
  simp only [TM0.step, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', st⟩, hM, rfl⟩ := h
  rw [head_toTape] at hM
  cases st with
  | move d =>
    refine ⟨hS.2 hM hq, t.move d, toTape_move t d, ?_⟩
    simp only [step, ofTM0_tr_of_eq_move M S hS hq hM]
    rfl
  | write a =>
    refine ⟨hS.2 hM hq, t.write ((Equiv.optionSubtypeNe default).symm a),
      by simp only [toTape_write, Equiv.apply_symm_apply], ?_⟩
    simp only [step, ofTM0_tr_of_eq_write M S hS hq hM]
    rfl

/-- **Runs of a TM0 machine are runs of its single-tape simulation.** Let $M$ be a TM0 machine
over a finite alphabet $\Gamma_0$ with blank symbol $b$ and at least one non-blank symbol,
supported by a finite set $S$ of states, and let $\widehat{M}$ be the single-tape machine over
the non-blank symbols $N = \Gamma_0 \setminus \{b\}$ simulating $M$. For a tape $t$ over $N$,
write $\tau(t)$ for the TM0 tape read from $t$ cell by cell. If $M$ goes from a configuration
$(q, T)$ to a configuration $(q', T')$ in exactly $n$ steps, $q \in S$, and $\tau(t) = T$, then
$q' \in S$ and there is a tape $t'$ over $N$ with $\tau(t') = T'$ such that $\widehat{M}$ goes
from the configuration $(q, t)$ to the configuration $(q', t')$ in exactly $n$ steps. -/
theorem relatesInSteps_ofTM0 {c c' : TM0.Cfg Γ₀ Λ} {n : ℕ}
    (h : RelatesInSteps (fun a b ↦ b ∈ TM0.step M a) c c' n) (hc : c.q ∈ S)
    {t : BiTape (NonBlank Γ₀)} (ht : toTape t = c.Tape) :
    ∃ (hc' : c'.q ∈ S) (t' : BiTape (NonBlank Γ₀)), toTape t' = c'.Tape ∧
      RelatesInSteps (ofTM0 M S hS).TransitionRelation ⟨some ⟨c.q, hc⟩, t⟩
        ⟨some ⟨c'.q, hc'⟩, t'⟩ n := by
  induction h with
  | refl => exact ⟨hc, t, ht, .refl _⟩
  | tail b b' n _ hstep ih =>
    obtain ⟨hb, tb, htb, hrun⟩ := ih
    have hstep' : TM0.step M ⟨b.q, toTape tb⟩ = some b' := by
      rw [htb]
      exact hstep
    obtain ⟨hb', t', ht', hst⟩ := step_ofTM0_of_step_eq_some M S hS hb hstep'
    exact ⟨hb', t', ht', hrun.tail _ _ _ _ hst⟩

/-- If `ofTM0 M S hS` halts from a supported state `q` and a tape `t`, then the `TM0` machine
halts from `q` and `toTape t`. -/
private theorem eval_dom_of_reflTransGen {a b : (ofTM0 M S hS).Cfg}
    (h : ReflTransGen (ofTM0 M S hS).TransitionRelation a b) (hb : b.state = none) :
    ∀ {q : Λ} (hq : q ∈ S) {t : BiTape (NonBlank Γ₀)}, a = ⟨some ⟨q, hq⟩, t⟩ →
      (eval (TM0.step M) ⟨q, toTape t⟩).Dom := by
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    rintro q hq t rfl
    simp at hb
  | head hab _ ih =>
    rintro q hq t rfl
    cases hM : TM0.step M ⟨q, toTape t⟩ with
    | none => exact Part.dom_iff_mem.2 ⟨_, mem_eval.2 ⟨.refl, hM⟩⟩
    | some c =>
      obtain ⟨hc, t', ht', hst⟩ := step_ofTM0_of_step_eq_some M S hS hq hM
      rw [reaches_eval (ReflTransGen.single hM)]
      have hab' : _ = _ := hab.symm.trans hst
      have := ih hc (Option.some_injective _ hab')
      rwa [ht'] at this

/-- A halting `TM0` run of `n` steps on `l`, ending in `c`, is a run of `n + 1` steps of
`ofTM0 M S hS` on `l` into its halting state, with a tape that reads as that of `c`. -/
private theorem relatesInSteps_ofTM0_halt {l : List (NonBlank Γ₀)} {c : TM0.Cfg Γ₀ Λ} {n : ℕ}
    (hc : RelatesInSteps (fun a b ↦ b ∈ TM0.step M a) (TM0.init (l.map Subtype.val)) c n)
    (hh : TM0.step M c = none) :
    ∃ t : BiTape (NonBlank Γ₀), toTape t = c.Tape ∧
      RelatesInSteps (ofTM0 M S hS).TransitionRelation ((ofTM0 M S hS).initCfg l) ⟨none, t⟩
        (n + 1) := by
  obtain ⟨hc', t, ht, hrun⟩ :=
    relatesInSteps_ofTM0 M S hS hc hS.1 (t := BiTape.mk₁ l) (toTape_mk₁ l)
  refine ⟨t, ht, hrun.tail _ _ _ _ (step_ofTM0_of_step_eq_none M S hS hc' ?_)⟩
  rw [ht]
  exact hh

/-- **The simulating machine halts exactly when the Post–Turing machine halts.** Let $\Gamma_0$
be a finite alphabet with at least one non-blank symbol, let $M$ be a Post–Turing machine over
$\Gamma_0$ supported by the finite set of states $S$, and let $l$ be a word of non-blank symbols
of $\Gamma_0$. The single-tape machine simulating $M$ halts on the input $l$ if and only if $M$,
started on $l$, halts. -/
theorem haltsOn_ofTM0_iff (l : List (NonBlank Γ₀)) :
    (ofTM0 M S hS).HaltsOn l ↔ (TM0.eval M (l.map Subtype.val)).Dom := by
  constructor
  · rintro ⟨c, h, hc⟩
    have := eval_dom_of_reflTransGen M S hS h hc hS.1 rfl
    rwa [toTape_mk₁] at this
  · intro h
    obtain ⟨c, hc⟩ := Part.dom_iff_mem.1
      (show (eval (TM0.step M) (TM0.init (l.map Subtype.val))).Dom from h)
    obtain ⟨hr, hh⟩ := mem_eval.1 hc
    obtain ⟨n, hn⟩ := ReflTransGen.relatesInSteps hr
    obtain ⟨t, -, hrun⟩ := relatesInSteps_ofTM0_halt M S hS hn hh
    exact ⟨_, hrun.reflTransGen, rfl⟩

/-- **The single-tape simulation outputs within one extra step.** Let $\Gamma_0$ be a finite
alphabet with at least one non-blank symbol, let $M$ be a Post–Turing machine over $\Gamma_0$
supported by the finite set of states $S$, and let $l$ and $l'$ be words of non-blank symbols of
$\Gamma_0$. If $M$, started on $l$, reaches in exactly $n$ steps a configuration $c$ in which it
halts, and the tape of $c$ holds $l'$ starting at the head with blanks everywhere else, then the
single-tape machine simulating $M$ outputs $l'$ on the input $l$ within $n + 1$ steps: its run
from the initial configuration on $l$ reaches, in at most $n + 1$ steps, the halting state with
the tape holding exactly $l'$, starting at the head. -/
theorem outputsWithinTime_ofTM0 {l l' : List (NonBlank Γ₀)} {c : TM0.Cfg Γ₀ Λ} {n : ℕ}
    (hc : RelatesInSteps (fun a b ↦ b ∈ TM0.step M a) (TM0.init (l.map Subtype.val)) c n)
    (hh : TM0.step M c = none) (ht : c.Tape = Tape.mk₁ (l'.map Subtype.val)) :
    (ofTM0 M S hS).OutputsWithinTime l l' (n + 1) := by
  obtain ⟨t, ht', hrun⟩ := relatesInSteps_ofTM0_halt M S hS hc hh
  obtain rfl : t = BiTape.mk₁ l' := toTape_injective (by rw [ht', ht, toTape_mk₁])
  exact RelatesWithinSteps.of_relatesInSteps hrun

/-- **The single-tape simulation has the same output.** Let $\Gamma_0$ be a finite alphabet with
at least one non-blank symbol, let $M$ be a Post–Turing machine over $\Gamma_0$ supported by the
finite set of states $S$, and let $l$ and $l'$ be words of non-blank symbols of $\Gamma_0$. If
$M$, started on $l$, halts in a configuration whose tape holds $l'$ starting at the head, with
blanks everywhere else, then the single-tape machine simulating $M$ outputs $l'$ on the input
$l$: its run from the initial configuration on $l$ reaches the halting state with the tape
holding exactly $l'$, starting at the head. -/
theorem outputs_ofTM0 {l l' : List (NonBlank Γ₀)} {c : TM0.Cfg Γ₀ Λ}
    (hc : c ∈ StateTransition.eval (TM0.step M) (TM0.init (l.map Subtype.val)))
    (ht : c.Tape = Tape.mk₁ (l'.map Subtype.val)) : (ofTM0 M S hS).Outputs l l' := by
  obtain ⟨hr, hh⟩ := mem_eval.1 hc
  obtain ⟨n, hn⟩ := ReflTransGen.relatesInSteps hr
  obtain ⟨m, -, hm⟩ := outputsWithinTime_ofTM0 M S hS hn hh ht
  exact hm.reflTransGen

end Cslib.Turing.SingleTapeTM
