/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Tactic.DeriveFintype
import CSLibExt.Computability.Machines.Turing.SingleTape.Classes
import CSLibExt.Computability.Machines.Turing.SingleTape.TapeView

/-!
# Canonical one-cell outputs after a marked single-tape simulation

`canonicalComputer tm` simulates an existing `SingleTapeTM`, then erases its working tape and
returns to the answer head. The input symbols are `Canonical.embed a`. Each source cell is
stored as `Canonical.Symbol.cell (Option Symbol)`: the source blank is a *nonblank* visited
marker. Consequently source erasures cannot hide dirty cells beyond blank gaps.

There is one initial normalization step and two steps per source transition: its write/move,
then a stationary normalization of the destination cell. The marked region grows by at most
one cell per source transition, by the actual `Cfg.spaceUsed_step` and `BiTape.spaceUsed_write`
lemmas. Cleanup takes exactly `2 * left.length + 2 * right.length + 5` steps: anchor the answer,
erase left, return, erase right, return and restore the ordinary answer symbol.

`canonicalComputer_outputsHeadWithinTime` needs only a timed halting source run and its head
symbol. It does not assume either half-tape is blank. Its conclusion uses the pinned canonical
`OutputsWithinTime` convention, with both half-tapes blank and the head on the answer.
-/

@[expose] public section

set_option autoImplicit false

open Relation
open _root_.Turing

namespace Cslib.Turing.SingleTapeTM

namespace Canonical

/-- The marked alphabet: an ordinary visited cell, or the unique cleanup answer anchor. -/
inductive Symbol (Γ : Type) where
  /-- A visited source cell; `cell none` marks a visited source blank. -/
  | cell (a : Option Γ)
  /-- The saved answer at the head position to which cleanup returns. -/
  | answer (a : Option Γ)
  deriving DecidableEq, Fintype

/-- The marked alphabet is inhabited even when the source alphabet is empty. -/
instance {Γ : Type} : Inhabited (Symbol Γ) := ⟨.cell none⟩

/-- The finite control of the marked simulation and its four cleanup passes. -/
inductive State (Q : Type) where
  /-- Normalize the initial head cell. -/
  | start
  /-- Execute one source transition. -/
  | run (q : Q)
  /-- Normalize the cell just reached, then resume or start cleanup. -/
  | mark (q : Option Q)
  /-- Save the answer anchor and start the left sweep. -/
  | cleanup
  /-- Erase left until the first unvisited blank. -/
  | eraseLeft
  /-- Return right through erased blanks to the answer anchor. -/
  | returnRight
  /-- Erase right until the first unvisited blank. -/
  | eraseRight
  /-- Return left to the anchor, restore the answer and halt. -/
  | returnLeft
  deriving DecidableEq, Fintype

/-- Read the source cell; an unvisited blank reads as a source blank. -/
def read {Γ : Type} : Option (Symbol Γ) → Option Γ
  | some (.cell a) | some (.answer a) => a
  | none => none

/-- Embed a source input or output symbol as an ordinary marked cell. -/
def embed {Γ : Type} (a : Γ) : Symbol Γ := .cell (some a)

/-- The input/output embedding preserves distinct symbols. -/
theorem embed_injective {Γ : Type} : Function.Injective (embed (Γ := Γ)) := by
  intro a b h
  cases h
  rfl

/-- A contiguous marked tape, including markers for the source blanks in its two lists. -/
def markedTape {Γ : Type} (a : Option Γ) (l r : List (Option Γ)) : BiTape (Symbol Γ) :=
  ⟨some (.cell a), StackTape.mapSome (l.map .cell), StackTape.mapSome (r.map .cell)⟩

end Canonical

variable {Γ : Type} [Inhabited Γ] [Fintype Γ]

/-- Simulate `tm` with visited-cell markers, then erase both halves and return to its answer head.
The source transition is followed by one stationary normalization step, including when it halts.
No cleanup state is reachable from the simulation unless the source enters its halting state. -/
abbrev canonicalComputer (tm : SingleTapeTM Γ) : SingleTapeTM (Canonical.Symbol Γ) where
  State := Canonical.State tm.State
  q₀ := .start
  tr
    | .start, a => (⟨some (.cell (Canonical.read a)), none⟩, some (.run tm.q₀))
    | .run q, a =>
      let s := tm.tr q (Canonical.read a)
      (⟨some (.cell s.1.symbol), s.1.movement⟩, some (.mark s.2))
    | .mark q, a =>
      (⟨some (.cell (Canonical.read a)), none⟩, some (q.elim .cleanup .run))
    | .cleanup, a => (⟨some (.answer (Canonical.read a)), some .left⟩, some .eraseLeft)
    | .eraseLeft, none => (⟨none, some .right⟩, some .returnRight)
    | .eraseLeft, some _ => (⟨none, some .left⟩, some .eraseLeft)
    | .returnRight, some (.answer a) => (⟨some (.answer a), some .right⟩, some .eraseRight)
    | .returnRight, _ => (⟨none, some .right⟩, some .returnRight)
    | .eraseRight, none => (⟨none, some .left⟩, some .returnLeft)
    | .eraseRight, some _ => (⟨none, some .right⟩, some .eraseRight)
    | .returnLeft, some (.answer a) => (⟨some (.cell a), none⟩, none)
    | .returnLeft, _ => (⟨none, some .left⟩, some .returnLeft)

namespace Canonical

variable (tm : SingleTapeTM Γ)

/-- An explicit finite view of the source cells; trailing source blanks are retained as markers. -/
private structure View (Γ : Type) where
  head : Option Γ
  left : List (Option Γ)
  right : List (Option Γ)

private def View.toTape (v : View Γ) : Tape (Option Γ) :=
  ⟨v.head, ListBlank.mk v.left, ListBlank.mk v.right⟩

private def View.markTape (v : View Γ) : BiTape (Symbol Γ) :=
  markedTape v.head v.left v.right

private def View.after (v : View Γ) (s : Stmt Γ) : View Γ :=
  match s.movement with
  | none => ⟨s.symbol, v.left, v.right⟩
  | some .left => ⟨v.left.headI, v.left.tail, s.symbol :: v.right⟩
  | some .right => ⟨v.right.headI, s.symbol :: v.left, v.right.tail⟩

private def stage (q : Option tm.State) : State tm.State := q.elim .cleanup .run

@[simp]
private theorem head_mapSome {α : Type} (l : List α) :
    (StackTape.mapSome l).head = l.head? := by
  cases l <;> rfl

@[simp]
private theorem tail_mapSome {α : Type} (l : List α) :
    (StackTape.mapSome l).tail = StackTape.mapSome l.tail := by
  cases l <;> rfl

@[simp]
private theorem cons_mapSome {α : Type} (a : α) (l : List α) :
    StackTape.cons (some a) (StackTape.mapSome l) = StackTape.mapSome (a :: l) := rfl

@[simp]
private theorem mapSome_nil {α : Type} :
    StackTape.mapSome ([] : List α) = StackTape.nil := rfl

@[simp]
private theorem head_nil {α : Type} : (StackTape.nil : StackTape α).head = none := rfl

@[simp]
private theorem tail_nil {α : Type} :
    (StackTape.nil : StackTape α).tail = StackTape.nil := rfl

@[simp]
private theorem cons_none_nil {α : Type} :
    StackTape.cons none (StackTape.nil : StackTape α) = StackTape.nil := rfl

omit [Inhabited Γ] [Fintype Γ] in
private theorem View.toTape_after (v : View Γ) (s : Stmt Γ) :
    (v.after s).toTape = s.movement.elim (v.toTape.write s.symbol)
      (fun d ↦ (v.toTape.write s.symbol).move d) := by
  rcases s with ⟨a, _ | (_ | _)⟩
  · rfl
  · simp [View.after, View.toTape, Tape.move, Tape.write, ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]
  · simp [View.after, View.toTape, Tape.move, Tape.write, ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]

omit [Inhabited Γ] [Fintype Γ] in
private theorem View.normalize_after (v : View Γ) (s : Stmt Γ) :
    let T := (v.markTape.write (some (.cell s.symbol))).optionMove s.movement
    T.write (some (.cell (read T.head))) = (v.after s).markTape := by
  dsimp only
  obtain ⟨h, l, r⟩ := v
  rcases s with ⟨a, _ | (_ | _)⟩
  · rfl
  · cases l <;> simp [View.markTape, markedTape, View.after, BiTape.write,
      BiTape.optionMove, BiTape.move, BiTape.moveLeft, read]
    rfl
  · cases r <;> simp [View.markTape, markedTape, View.after, BiTape.write,
      BiTape.optionMove, BiTape.move, BiTape.moveRight, read]
    rfl

/-- One real write/move and one stationary mark implement exactly one source transition. -/
private theorem macro_step (q : tm.State) (v : View Γ) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some (.run q), v.markTape⟩
      ⟨some (stage tm (tm.tr q v.head).2), (v.after (tm.tr q v.head).1).markTape⟩ 2 ∧
    (v.after (tm.tr q v.head).1).markTape.spaceUsed ≤ v.markTape.spaceUsed + 1 := by
  let s := tm.tr q v.head
  let T := (v.markTape.write (some (.cell s.1.symbol))).optionMove s.1.movement
  have h₁ : tm.canonicalComputer.TransitionRelation ⟨some (.run q), v.markTape⟩
      ⟨some (.mark s.2), T⟩ := rfl
  have hT : T.write (some (.cell (read T.head))) = (v.after s.1).markTape :=
    v.normalize_after s.1
  have h₂ : tm.canonicalComputer.TransitionRelation ⟨some (.mark s.2), T⟩
      ⟨some (stage tm s.2), (v.after s.1).markTape⟩ := by
    change some (⟨some (stage tm s.2), T.write (some (.cell (read T.head)))⟩ :
      tm.canonicalComputer.Cfg) = _
    rw [hT]
  refine ⟨(RelatesInSteps.single h₁).trans (.single h₂), ?_⟩
  have hspace := Cfg.spaceUsed_step (tm := tm.canonicalComputer) _ _ h₁
  change T.spaceUsed ≤ v.markTape.spaceUsed + 1 at hspace
  calc
    (v.after s.1).markTape.spaceUsed = (T.write (some (.cell (read T.head)))).spaceUsed :=
      congrArg BiTape.spaceUsed hT.symm
    _ = T.spaceUsed := BiTape.spaceUsed_write _ _
    _ ≤ v.markTape.spaceUsed + 1 := hspace

/-- Simulation preserves the source tape view and bounds the whole marked visited region. -/
private theorem simulate {a b : tm.Cfg} {n : ℕ}
    (hr : RelatesInSteps tm.TransitionRelation a b n) {v₀ : View Γ}
    (hv₀ : a.BiTape.toTape = v₀.toTape) :
    ∃ v : View Γ, b.BiTape.toTape = v.toTape ∧
      RelatesInSteps tm.canonicalComputer.TransitionRelation
        ⟨some (stage tm a.state), v₀.markTape⟩ ⟨some (stage tm b.state), v.markTape⟩ (2 * n) ∧
      v.markTape.spaceUsed ≤ v₀.markTape.spaceUsed + n := by
  induction hr with
  | refl => exact ⟨v₀, hv₀, .refl _, by omega⟩
  | tail b b' n _ hstep ih =>
    obtain ⟨v, hv, hrun, hspace⟩ := ih
    obtain ⟨_ | q, T⟩ := b
    · cases hstep
    have hh : T.head = v.head := congrArg Tape.head hv
    rw [TransitionRelation, step_some, hh] at hstep
    obtain rfl := Option.some_injective _ hstep
    obtain ⟨hmacro, hmacrospace⟩ := macro_step tm q v
    refine ⟨v.after (tm.tr q v.head).1, ?_, ?_, hmacrospace.trans (by omega)⟩
    · rw [BiTape.toTape_optionMove, BiTape.toTape_write, hv]
      exact (v.toTape_after _).symm
    · simpa [stage, Nat.mul_add, Nat.add_assoc] using hrun.trans hmacro

/-! ### The four counted cleanup passes -/

private def blanks (n : ℕ) (s : StackTape (Symbol Γ)) : StackTape (Symbol Γ) :=
  (StackTape.cons none)^[n] s

omit [Inhabited Γ] [Fintype Γ] in
private theorem blanks_succ (n : ℕ) (s : StackTape (Symbol Γ)) :
    blanks (n + 1) s = StackTape.cons none (blanks n s) :=
  Function.iterate_succ_apply' _ n s

private def leftScan (l : List (Option Γ)) (s : StackTape (Symbol Γ)) : BiTape (Symbol Γ) :=
  match l with
  | [] => ⟨none, ∅, s⟩
  | a :: l => ⟨some (.cell a), StackTape.mapSome (l.map .cell), s⟩

private def rightScan (r : List (Option Γ)) (s : StackTape (Symbol Γ)) : BiTape (Symbol Γ) :=
  match r with
  | [] => ⟨none, s, ∅⟩
  | a :: r => ⟨some (.cell a), s, StackTape.mapSome (r.map .cell)⟩

private theorem return_right (a : Option Γ) (R : StackTape (Symbol Γ)) (n : ℕ) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some .returnRight, ⟨none, ∅, blanks n (StackTape.cons (some (.answer a)) R)⟩⟩
      ⟨some .eraseRight, (⟨some (.answer a), ∅, R⟩ : BiTape (Symbol Γ)).moveRight⟩ (n + 2) := by
  induction n with
  | zero =>
    exact (RelatesInSteps.single (show tm.canonicalComputer.TransitionRelation
      ⟨some .returnRight, ⟨none, ∅, StackTape.cons (some (.answer a)) R⟩⟩
      ⟨some .returnRight, ⟨some (.answer a), ∅, R⟩⟩ from by
        simp [TransitionRelation, canonicalComputer, BiTape.optionMove, BiTape.move,
          BiTape.moveRight, BiTape.write])).tail _ _ _ _ rfl
  | succ n ih =>
    rw [blanks_succ]
    have h : tm.canonicalComputer.TransitionRelation
        ⟨some .returnRight, ⟨none, ∅,
          StackTape.cons none (blanks n (StackTape.cons (some (.answer a)) R))⟩⟩
        ⟨some .returnRight, ⟨none, ∅, blanks n (StackTape.cons (some (.answer a)) R)⟩⟩ := by
      simp [TransitionRelation, canonicalComputer, BiTape.optionMove, BiTape.move,
        BiTape.moveRight, BiTape.write]
    rw [show n + 1 + 2 = 1 + (n + 2) by omega]
    exact (RelatesInSteps.single h).trans ih

private theorem erase_left (a : Option Γ) (R : StackTape (Symbol Γ))
    (l : List (Option Γ)) (n : ℕ) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some .eraseLeft, leftScan l (blanks n (StackTape.cons (some (.answer a)) R))⟩
      ⟨some .eraseRight, (⟨some (.answer a), ∅, R⟩ : BiTape (Symbol Γ)).moveRight⟩
      (2 * l.length + n + 2) := by
  induction l generalizing n with
  | nil =>
    have hr := return_right tm a R n
    obtain ⟨d, h, hd⟩ := hr.succ'
    have h' : tm.canonicalComputer.TransitionRelation
        ⟨some .eraseLeft, leftScan [] (blanks n (StackTape.cons (some (.answer a)) R))⟩ d := h
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using hd.head _ _ _ _ h'
  | cons b l ih =>
    have h : tm.canonicalComputer.TransitionRelation
        ⟨some .eraseLeft, leftScan (b :: l) (blanks n (StackTape.cons (some (.answer a)) R))⟩
        ⟨some .eraseLeft, leftScan l (blanks (n + 1) (StackTape.cons (some (.answer a)) R))⟩ := by
      cases l <;> simp [TransitionRelation, canonicalComputer, leftScan, blanks_succ,
        BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.write]
    rw [List.length_cons,
      show 2 * (l.length + 1) + n + 2 = 1 + (2 * l.length + (n + 1) + 2) by omega]
    exact (RelatesInSteps.single h).trans (ih (n + 1))

private theorem return_left (a : Option Γ) (n : ℕ) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some .returnLeft, ⟨none, blanks n (StackTape.cons (some (.answer a)) ∅), ∅⟩⟩
      (tm.canonicalComputer.haltCfg [.cell a]) (n + 2) := by
  induction n with
  | zero =>
    exact (RelatesInSteps.single (show tm.canonicalComputer.TransitionRelation
      ⟨some .returnLeft, ⟨none, StackTape.cons (some (.answer a)) ∅, ∅⟩⟩
      ⟨some .returnLeft, ⟨some (.answer a), ∅, ∅⟩⟩ from by
        simp [TransitionRelation, canonicalComputer, BiTape.optionMove, BiTape.move,
          BiTape.moveLeft, BiTape.write])).tail _ _ _ _ rfl
  | succ n ih =>
    rw [blanks_succ]
    have h : tm.canonicalComputer.TransitionRelation
        ⟨some .returnLeft, ⟨none,
          StackTape.cons none (blanks n (StackTape.cons (some (.answer a)) ∅)), ∅⟩⟩
        ⟨some .returnLeft, ⟨none, blanks n (StackTape.cons (some (.answer a)) ∅), ∅⟩⟩ := by
      simp [TransitionRelation, canonicalComputer, BiTape.optionMove, BiTape.move,
        BiTape.moveLeft, BiTape.write]
    rw [show n + 1 + 2 = 1 + (n + 2) by omega]
    exact (RelatesInSteps.single h).trans ih

private theorem erase_right (a : Option Γ) (r : List (Option Γ)) (n : ℕ) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some .eraseRight, rightScan r (blanks n (StackTape.cons (some (.answer a)) ∅))⟩
      (tm.canonicalComputer.haltCfg [.cell a]) (2 * r.length + n + 2) := by
  induction r generalizing n with
  | nil =>
    have hr := return_left tm a n
    obtain ⟨d, h, hd⟩ := hr.succ'
    have h' : tm.canonicalComputer.TransitionRelation
        ⟨some .eraseRight, rightScan [] (blanks n (StackTape.cons (some (.answer a)) ∅))⟩ d := h
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using hd.head _ _ _ _ h'
  | cons b r ih =>
    have h : tm.canonicalComputer.TransitionRelation
        ⟨some .eraseRight, rightScan (b :: r) (blanks n (StackTape.cons (some (.answer a)) ∅))⟩
        ⟨some .eraseRight, rightScan r (blanks (n + 1) (StackTape.cons (some (.answer a)) ∅))⟩ := by
      cases r <;> simp [TransitionRelation, canonicalComputer, rightScan, blanks_succ,
        BiTape.optionMove, BiTape.move, BiTape.moveRight, BiTape.write]
    rw [List.length_cons,
      show 2 * (r.length + 1) + n + 2 = 1 + (2 * r.length + (n + 1) + 2) by omega]
    exact (RelatesInSteps.single h).trans (ih (n + 1))

/-- Cleanup erases every marked cell on both sides, including marked source blanks, and returns
exactly to the answer head. The precise cost counts both outward and return traversals. -/
theorem cleanup_relatesInSteps (a : Option Γ) (l r : List (Option Γ)) :
    RelatesInSteps tm.canonicalComputer.TransitionRelation
      ⟨some .cleanup, markedTape a l r⟩ (tm.canonicalComputer.haltCfg [.cell a])
      (2 * l.length + 2 * r.length + 5) := by
  let R := StackTape.mapSome (r.map Symbol.cell)
  have h₀ : tm.canonicalComputer.TransitionRelation ⟨some .cleanup, markedTape a l r⟩
      ⟨some .eraseLeft, leftScan l (StackTape.cons (some (.answer a)) R)⟩ := by
    cases l <;> simp [TransitionRelation, canonicalComputer, markedTape, leftScan, R, read,
      BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.write]
  have h₁ := erase_left tm a R l 0
  have h₂ := erase_right tm a r 0
  have hmid : (⟨some (.answer a), ∅, R⟩ : BiTape (Symbol Γ)).moveRight =
      rightScan r (StackTape.cons (some (.answer a)) ∅) := by
    cases r <;> simp [R, rightScan, BiTape.moveRight]
  rw [hmid] at h₁
  simp only [blanks, Function.iterate_zero, id_eq, Nat.add_zero] at h₁ h₂
  rw [show 2 * l.length + 2 * r.length + 5 =
    (1 + (2 * l.length + 2)) + (2 * r.length + 2) by omega]
  exact ((RelatesInSteps.single h₀).trans h₁).trans h₂

private def inputView (l : List Γ) : View Γ := ⟨l.head?, [], l.tail.map some⟩

omit [Inhabited Γ] [Fintype Γ] in
private theorem inputView_toTape (l : List Γ) : (BiTape.mk₁ l).toTape = (inputView l).toTape := by
  cases l <;> rfl

private theorem initial_step (l : List Γ) :
    tm.canonicalComputer.TransitionRelation (tm.canonicalComputer.initCfg (l.map embed))
      ⟨some (.run tm.q₀), (inputView l).markTape⟩ := by
  cases l <;> simp [TransitionRelation, canonicalComputer, initCfg, inputView, View.markTape,
    markedTape, embed, read, BiTape.mk₁, BiTape.nil, BiTape.write, BiTape.optionMove,
    List.map_map, Function.comp_def]
  rfl

omit [Inhabited Γ] [Fintype Γ] in
private theorem inputView_spaceUsed (l : List Γ) :
    (inputView l).markTape.spaceUsed = max 1 l.length := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [inputView, View.markTape, markedTape, BiTape.spaceUsed, StackTape.length_mapSome,
      List.length_map, List.tail_cons, List.length_nil, List.length_cons, Nat.add_zero]
    omega

end Canonical

/-- A timed source halting run with answer `a` under its head gives a canonical one-cell output.
No condition is imposed on the source left or right halves, or on termination of other runs. -/
theorem canonicalComputer_outputsHeadWithinTime (tm : SingleTapeTM Γ) {l : List Γ}
    {b : tm.Cfg} {T : ℕ} {a : Γ}
    (hr : RelatesWithinSteps tm.TransitionRelation (tm.initCfg l) b T)
    (hb : b.state = none) (ha : b.BiTape.head = some a) :
    tm.canonicalComputer.OutputsWithinTime (l.map Canonical.embed) [Canonical.embed a]
      (4 * T + 2 * l.length + 6) := by
  obtain ⟨j, hj, hrun⟩ := hr
  obtain ⟨v, hv, hsim, hspace⟩ := Canonical.simulate tm hrun (Canonical.inputView_toTape l)
  have hhead : v.head = some a := (congrArg Tape.head hv).symm.trans ha
  have hclean := Canonical.cleanup_relatesInSteps tm v.head v.left v.right
  rw [hb] at hsim
  have hfull := ((RelatesInSteps.single (Canonical.initial_step tm l)).trans hsim).trans hclean
  have hout : tm.canonicalComputer.OutputsWithinTime (l.map Canonical.embed) [Canonical.embed a]
      ((1 + 2 * j) + (2 * v.left.length + 2 * v.right.length + 5)) := by
    simpa only [OutputsWithinTime, Canonical.embed, hhead] using
      RelatesWithinSteps.of_relatesInSteps hfull
  refine RelatesWithinSteps.mono ?_ hout
  rw [Canonical.inputView_spaceUsed] at hspace
  simp only [Canonical.View.markTape, Canonical.markedTape, BiTape.spaceUsed,
    StackTape.length_mapSome, List.length_map] at hspace
  have hmax : max 1 l.length ≤ l.length + 1 := by omega
  omega

end Cslib.Turing.SingleTapeTM
