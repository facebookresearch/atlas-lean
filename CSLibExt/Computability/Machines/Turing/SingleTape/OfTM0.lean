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

/-- The non-blank symbols of a `TM0` alphabet: the tape alphabet of the simulating machine. -/
abbrev NonBlank (Γ₀ : Type) [Inhabited Γ₀] : Type := {x : Γ₀ // x ≠ default}

section Tape

variable [DecidableEq Γ₀]

/-- A cell over the non-blank symbols read as a `TM0` symbol, the blank cell `none` being the
blank symbol `default`: the pointed map `Equiv.optionSubtypeNe default`. -/
def cellSymbol : PointedMap (Option (NonBlank Γ₀)) Γ₀ :=
  ⟨Equiv.optionSubtypeNe default, rfl⟩

/-- `cellSymbol` reads a cell through `Equiv.optionSubtypeNe default`. -/
@[simp]
theorem cellSymbol_apply (o : Option (NonBlank Γ₀)) :
    cellSymbol o = Equiv.optionSubtypeNe default o :=
  rfl

/-- `cellSymbol` is injective. -/
theorem cellSymbol_injective : Function.Injective (cellSymbol (Γ₀ := Γ₀)) :=
  (Equiv.optionSubtypeNe default).injective

/-- Read a `StackTape` over the non-blank symbols as a `TM0` half-tape, cell by cell: the cells of
`StackTape.toListBlank` through `cellSymbol`. -/
def toListBlank (s : StackTape (NonBlank Γ₀)) : ListBlank Γ₀ :=
  s.toListBlank.map cellSymbol

/-- Read a `BiTape` over the non-blank symbols as a `TM0` tape, cell by cell: the cells of
`BiTape.toTape` through `cellSymbol`. -/
def toTape (t : BiTape (NonBlank Γ₀)) : Tape Γ₀ :=
  t.toTape.map cellSymbol

/-- The empty `StackTape` reads as the all-blank half-tape. -/
@[simp]
theorem toListBlank_nil : toListBlank (StackTape.nil : StackTape (NonBlank Γ₀)) = ListBlank.mk [] :=
  rfl

/-- Pushing a cell onto a `StackTape` pushes its symbol onto the half-tape; for the blank cell
this holds because the half-tape is blank beyond its end. -/
@[simp]
theorem toListBlank_cons (o : Option (NonBlank Γ₀)) (s : StackTape (NonBlank Γ₀)) :
    toListBlank (StackTape.cons o s) =
      (toListBlank s).cons (Equiv.optionSubtypeNe default o) := by
  simp [toListBlank, ListBlank.map_cons]

/-- The first symbol of the half-tape is that of the first cell. -/
@[simp]
theorem head_toListBlank (s : StackTape (NonBlank Γ₀)) :
    (toListBlank s).head = Equiv.optionSubtypeNe default s.head := by
  simp [toListBlank, ListBlank.head_map]

/-- Dropping the first cell drops the first symbol of the half-tape. -/
@[simp]
theorem tail_toListBlank (s : StackTape (NonBlank Γ₀)) :
    (toListBlank s).tail = toListBlank s.tail := by
  simp [toListBlank, ListBlank.tail_map]

/-- A word of non-blank symbols reads as itself. -/
@[simp]
theorem toListBlank_mapSome (l : List (NonBlank Γ₀)) :
    toListBlank (StackTape.mapSome l) = ListBlank.mk (l.map Subtype.val) := by
  simp [toListBlank, ListBlank.map_mk, Function.comp_def]

/-- A pointed map that is injective on symbols is injective on half-tapes. Generic; it could
become `Turing.ListBlank.map_injective` (with `Turing.Tape.map_injective`) in MathlibExt. -/
private theorem listBlank_map_injective {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    {f : PointedMap Γ Γ'} (hf : Function.Injective f) : Function.Injective (ListBlank.map f) :=
  fun _ _ h ↦ ListBlank.ext fun i ↦ hf (by rw [← ListBlank.nth_map, ← ListBlank.nth_map, h])

/-- `toListBlank` is injective: a `StackTape` does not end in a blank, so trailing blanks of a
half-tape do not come from cells. -/
theorem toListBlank_injective : Function.Injective (toListBlank (Γ₀ := Γ₀)) :=
  (listBlank_map_injective cellSymbol_injective).comp StackTape.toListBlank_injective

/-- The symbol under the head of `toTape t` is that of the head cell of `t`. -/
@[simp]
theorem head_toTape (t : BiTape (NonBlank Γ₀)) :
    (toTape t).head = Equiv.optionSubtypeNe default t.head :=
  rfl

/-- `toTape` turns writing a cell into writing its symbol. -/
@[simp]
theorem toTape_write (t : BiTape (NonBlank Γ₀)) (o : Option (NonBlank Γ₀)) :
    toTape (t.write o) = (toTape t).write (Equiv.optionSubtypeNe default o) := by
  rw [toTape, BiTape.toTape_write, Tape.map_write, cellSymbol_apply, toTape]

/-- `toTape` commutes with moving the head. -/
@[simp]
theorem toTape_move (t : BiTape (NonBlank Γ₀)) (d : Dir) :
    toTape (t.move d) = (toTape t).move d := by
  rw [toTape, BiTape.toTape_move, Tape.map_move, toTape]

/-- `toTape` commutes with an optional move of the head. -/
theorem toTape_optionMove (t : BiTape (NonBlank Γ₀)) (d : Option Dir) :
    toTape (t.optionMove d) = d.elim (toTape t) fun d ↦ (toTape t).move d := by
  cases d <;> simp [BiTape.optionMove]

/-- The input tape of a word of non-blank symbols reads as the `TM0` input tape of the word. -/
@[simp]
theorem toTape_mk₁ (l : List (NonBlank Γ₀)) :
    toTape (BiTape.mk₁ l) = Tape.mk₁ (l.map Subtype.val) := by
  simp [toTape, Tape.map_mk₁, Function.comp_def]

/-- `toTape` is injective. -/
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

/-- The single-tape machine running the `TM0` machine `M`, supported by `S`, step for step. Its
states are the elements of `S`, and it reads a cell `s` as the symbol
`Equiv.optionSubtypeNe default s`. A `TM0` move writes `s` back and moves; a `TM0` write of `a`
writes the cell of `a`; where `M` halts, the machine writes `s` back and halts. CSLib machines need
an inhabited alphabet, hence the instance `Inhabited (NonBlank Γ₀)`: an alphabet whose only
symbol is the blank is excluded. -/
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

/-- Where the `TM0` machine halts in a supported state, `ofTM0 M S hS` takes one step into its
halting state and leaves the tape unchanged. -/
theorem step_ofTM0_of_step_eq_none {q : Λ} (hq : q ∈ S) {t : BiTape (NonBlank Γ₀)}
    (h : TM0.step M ⟨q, toTape t⟩ = none) :
    (ofTM0 M S hS).step ⟨some ⟨q, hq⟩, t⟩ = some ⟨none, t⟩ := by
  have hM : M q (Equiv.optionSubtypeNe default t.head) = none := by
    simpa [TM0.step] using h
  simp only [step, ofTM0_tr_of_eq_none M S hS hq hM]
  rfl

/-- A `TM0` step from a supported state is one step of `ofTM0 M S hS`, between configurations
whose tapes correspond. -/
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

/-- A run of `n` `TM0` steps from a supported state is a run of `n` steps of `ofTM0 M S hS`,
between configurations whose tapes correspond. -/
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

/-- `ofTM0 M S hS` halts on `l` exactly when the `TM0` machine `M` halts on `l`. -/
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

/-- A `TM0` run of `n` steps on `l` that halts with the tape `Tape.mk₁ l'` makes `ofTM0 M S hS`
output `l'` on `l` within `n + 1` steps. -/
theorem outputsWithinTime_ofTM0 {l l' : List (NonBlank Γ₀)} {c : TM0.Cfg Γ₀ Λ} {n : ℕ}
    (hc : RelatesInSteps (fun a b ↦ b ∈ TM0.step M a) (TM0.init (l.map Subtype.val)) c n)
    (hh : TM0.step M c = none) (ht : c.Tape = Tape.mk₁ (l'.map Subtype.val)) :
    (ofTM0 M S hS).OutputsWithinTime l l' (n + 1) := by
  obtain ⟨t, ht', hrun⟩ := relatesInSteps_ofTM0_halt M S hS hc hh
  obtain rfl : t = BiTape.mk₁ l' := toTape_injective (by rw [ht', ht, toTape_mk₁])
  exact RelatesWithinSteps.of_relatesInSteps hrun

/-- When the `TM0` machine `M` halts on `l` with the tape `Tape.mk₁ l'`, `ofTM0 M S hS` outputs
`l'` on `l`. -/
theorem outputs_ofTM0 {l l' : List (NonBlank Γ₀)} {c : TM0.Cfg Γ₀ Λ}
    (hc : c ∈ StateTransition.eval (TM0.step M) (TM0.init (l.map Subtype.val)))
    (ht : c.Tape = Tape.mk₁ (l'.map Subtype.val)) : (ofTM0 M S hS).Outputs l l' := by
  obtain ⟨hr, hh⟩ := mem_eval.1 hc
  obtain ⟨n, hn⟩ := ReflTransGen.relatesInSteps hr
  obtain ⟨m, -, hm⟩ := outputsWithinTime_ofTM0 M S hS hn hh ht
  exact hm.reflTransGen

end Cslib.Turing.SingleTapeTM
