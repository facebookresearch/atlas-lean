/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.OfTM0
public import CSLibExt.Computability.Machines.Turing.Universal.Diagonalization

/-!
# Codes on CSLib's single-tape machines

A `Code` denotes a Mathlib `TM0` machine over the alphabet `ℕ` (`Code.machine`), and the time
classes `CodeTime t` count its steps (`Code.DecidesWithin`). This file runs every code on one of
CSLib's single-tape machines (`Cslib.Turing.SingleTapeTM`), step for step, and states what a
code that decides `L` within `t` gives on that machine.

A run of a code on bits only holds symbols below `c.symBound`: the blank `0`, the input symbols
`1` and `2`, and the symbols its table writes. `Code.finMachine c` is `c.machine` on the finite
alphabet `Fin c.symBound`, and `Code.singleTapeTM c` runs it on a `SingleTapeTM` through
`SingleTapeTM.ofTM0`. Its input word for the bits `x` is `x.map c.inputSym`, where
`c.inputSym b` is the symbol `bitSym b`.

## Main definitions

- `Cslib.Turing.Universal.Code.symBound`: the alphabet size of a code.
- `Cslib.Turing.Universal.Code.finMachine`: the machine of a code on the alphabet
  `Fin c.symBound`.
- `Cslib.Turing.Universal.Code.singleTapeTM`, `Cslib.Turing.Universal.Code.inputSym`: the
  single-tape machine of a code and its input symbols.

## Main results

- `Code.step_finMachine`: `c.finMachine` steps as `c.machine`, read through `Fin.val`.
- `Code.exists_relatesWithinSteps_singleTapeTM`: if `c` halts on `x` within `T` steps, its
  single-tape machine halts on the input word of `x` within `T + 1` steps, with a tape that reads
  as the tape of `c` after `T` steps.
- `Code.DecidesWithin.exists_relatesWithinSteps_singleTapeTM`: if `c` decides `L` within `t`,
  its single-tape machine halts on the input word of every `x` within `t |x| + 1` steps, with the
  answer symbol `c.inputSym (L x)` under the head, every cell right of the head blank, and the
  cells left of the head of `c` after `t |x|` steps left of its head.
- `Code.DecidesWithin.outputsWithinTime_singleTapeTM`: if moreover every cell left of the head of
  `c` is blank after `t |x|` steps on `x`, the single-tape machine outputs `[c.inputSym (L x)]`
  on the input word of `x` within `t |x| + 1` steps, in the sense of
  `SingleTapeTM.OutputsWithinTime`.
- `Code.DecidesWithin.outputs_singleTapeTM_iff`: if `c` decides `L` within `t`, the single-tape
  machine outputs `[c.inputSym (L x)]` on the input word of `x`, after some finite number of
  steps, exactly when every cell left of the head of `c` is blank after `t |x|` steps on `x`.

## The output conventions

`Code.DecidesWithin` reads the answer from the cells at and right of the head and ignores the
cells left of the head, while `SingleTapeTM.OutputsWithinTime` asks for a halting tape that holds
exactly the answer. So the single-tape machine of a code that decides `L` within `t` meets CSLib's
output convention exactly on the inputs where the code leaves the cells left of its head blank,
and there within `t |x| + 1` steps. To meet the convention on every input, a machine can follow
the simulation with a pass that erases those cells over the region the code visited; that
machine, and a class-level statement relating `CodeTime t` to single-tape machines in CSLib's
output convention, are not built here.
-/

@[expose] public section

set_option autoImplicit false

open _root_.Turing Relation MetaMathlibExt.ComplexityTheory

namespace Cslib.Turing.Universal

open Cslib.Turing.SingleTapeTM (NonBlank ofTM0 toTape toListBlank)

namespace Code

/-! ### A finite alphabet for a code -/

/-- The largest action number in the table of `c`, and `0` if the table has no transition.
Writing the symbol `a` has the action number `a + 2`. -/
def maxAction (c : Code) : ℕ := (c.table.flatten.filterMap fun o ↦ o.map Prod.snd).foldr max 0

/-- The alphabet size of `c`: every symbol that a run of `c` on bits can hold is below
`c.symBound`, namely the blank `0`, the input symbols `1` and `2`, and the symbols written by the
table. -/
abbrev symBound (c : Code) : ℕ := c.maxAction + 3

/-- An element of a list of numbers is at most its fold by `max`. -/
private theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- The symbols written by the table of `c` are below `c.symBound`. -/
theorem lt_symBound_of_machine_eq_write {c : Code} {q a q' w : ℕ}
    (h : c.machine q a = some (q', .write w)) : w < c.symBound := by
  simp only [machine, lookup, Option.map_eq_some_iff, Option.join_eq_some_iff,
    Option.bind_eq_some_iff] at h
  obtain ⟨⟨q'', s⟩, ⟨row, hrow, he⟩, hs⟩ := h
  have hmem : s ∈ c.table.flatten.filterMap fun o ↦ o.map Prod.snd :=
    List.mem_filterMap.2 ⟨some (q'', s),
      List.mem_flatten.2 ⟨row, List.mem_of_getElem? hrow, List.mem_of_getElem? he⟩, rfl⟩
  have hle : s ≤ c.maxAction := le_foldr_max hmem
  simp only [Prod.mk.injEq] at hs
  obtain ⟨-, hs⟩ := hs
  rcases s with _ | _ | w'
  · cases hs
  · cases hs
  · cases hs
    change _ < c.maxAction + 3
    omega

/-- A number as a symbol of the alphabet of `c`, taken modulo `c.symBound`; below `c.symBound` it
is the symbol with that value. -/
def toSym (c : Code) : PointedMap ℕ (Fin c.symBound) :=
  ⟨fun a ↦ ⟨a % c.symBound, Nat.mod_lt _ (Nat.succ_pos _)⟩, Fin.ext (Nat.zero_mod _)⟩

/-- A symbol of the alphabet of `c` as a number. -/
def symVal (c : Code) : PointedMap (Fin c.symBound) ℕ :=
  ⟨Fin.val, rfl⟩

/-- `symVal` is `Fin.val`. -/
@[simp]
theorem symVal_apply (c : Code) (a : Fin c.symBound) : c.symVal a = a.val :=
  rfl

/-- `symVal` is injective. -/
theorem symVal_injective (c : Code) : Function.Injective c.symVal :=
  Fin.val_injective

/-- The machine of `c` on the alphabet `Fin c.symBound`: it reads a symbol as its value and writes
the symbols that `c.machine` writes. -/
def finMachine (c : Code) : TM0.Machine (Fin c.symBound) ℕ := fun q a ↦
  (c.machine q a.val).map fun p ↦ (p.1, p.2.map c.toSym)

/-- **`c.finMachine` steps as `c.machine`**, on every configuration, read through `symVal`. -/
theorem step_finMachine (c : Code) (d : TM0.Cfg (Fin c.symBound) ℕ) :
    TM0.step c.machine (d.map c.symVal id) =
      (TM0.step c.finMachine d).map (TM0.Cfg.map c.symVal id) := by
  obtain ⟨q, T⟩ := d
  simp only [TM0.Cfg.map, TM0.step, Tape.map_fst, finMachine, Option.map_map, symVal_apply,
    id_eq]
  cases h : c.machine q T.head.val with
  | none => rfl
  | some p =>
    obtain ⟨q', st⟩ := p
    cases st with
    | move d => simp [TM0.Stmt.map, TM0.Cfg.map, Tape.map_move]
    | write w =>
      have hw := lt_symBound_of_machine_eq_write h
      simp [TM0.Stmt.map, TM0.Cfg.map, Tape.map_write, toSym, Nat.mod_eq_of_lt hw]

/-- `c.finMachine` is supported by the states of `c`. -/
theorem supports_finMachine (c : Code) : TM0.Supports c.finMachine ↑c.states := by
  refine ⟨c.supports_machine.1, fun {q a q' s} h hq ↦ ?_⟩
  simp only [finMachine, Option.mem_def, Option.map_eq_some_iff] at h
  obtain ⟨⟨q'', s'⟩, h', hq'⟩ := h
  simp only [Prod.mk.injEq] at hq'
  obtain ⟨rfl, -⟩ := hq'
  exact c.supports_machine.2 h' hq

/-- The alphabet of `c` has the non-blank symbol `1`. -/
instance (c : Code) : Inhabited (NonBlank (Fin c.symBound)) :=
  ⟨⟨⟨1, by simp⟩, fun h ↦ absurd (congrArg Fin.val h) (by simp)⟩⟩

/-- The single-tape machine of `c`: `c.finMachine` run on a CSLib single-tape machine by
`SingleTapeTM.ofTM0`, whose states are the states of `c`. -/
def singleTapeTM (c : Code) : SingleTapeTM (NonBlank (Fin c.symBound)) :=
  ofTM0 c.finMachine c.states c.supports_finMachine

/-- The symbol of the input bit `b` in the alphabet of `c`: the symbol `bitSym b`, which is not
blank. -/
def inputSym (c : Code) (b : Bool) : NonBlank (Fin c.symBound) :=
  ⟨⟨bitSym b, by cases b <;> simp [bitSym]⟩,
    fun h ↦ absurd (congrArg Fin.val h) (by cases b <;> simp [bitSym])⟩

/-- The value of an input symbol is the symbol of the bit. -/
@[simp]
theorem val_inputSym (c : Code) (b : Bool) : (c.inputSym b).val.val = bitSym b :=
  rfl

/-- Distinct bits have distinct input symbols. -/
theorem inputSym_injective (c : Code) : Function.Injective c.inputSym := by
  intro a b h
  have h' : bitSym a = bitSym b := congrArg (fun s : NonBlank (Fin c.symBound) ↦ s.val.val) h
  cases a <;> cases b <;> simp [bitSym] at h' ⊢

/-- The input word of `x` reads as the input of `x`. -/
theorem map_symVal_inputSym (c : Code) (x : List Bool) :
    ((x.map c.inputSym).map Subtype.val).map c.symVal = input x := by
  simp [input, Function.comp_def]

/-! ### Running a code on its single-tape machine -/

/-- The configuration after `n` clocked steps is reached in some `j ≤ n` steps. -/
private theorem exists_iterate_eq_cfgAfter (c : Code) (x : List Bool) (n : ℕ) :
    ∃ j ≤ n, (flip bind c.step)^[j] (some (init x)) = some (c.cfgAfter x n) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨j, hj, hjk⟩ := ih
    have hsucc : c.cfgAfter x (n + 1) = c.stepOrStay (c.cfgAfter x n) := by
      simp only [cfgAfter, Function.iterate_succ_apply']
    cases hs : c.step (c.cfgAfter x n) with
    | none =>
      refine ⟨j, by omega, ?_⟩
      rw [hjk, hsucc, stepOrStay, hs, Option.getD_none]
    | some k =>
      refine ⟨j + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', hjk, hsucc, stepOrStay, hs, Option.getD_some]
      exact hs

/-- An iterate of a step function that reaches `b` from `a` in `n` steps is a run of `n` steps. -/
private theorem relatesInSteps_of_iterate {σ : Type*} {f : σ → Option σ} {a : σ} :
    ∀ {n : ℕ} {b : σ}, (flip bind f)^[n] (some a) = some b →
      RelatesInSteps (fun a b ↦ b ∈ f a) a b n
  | 0, b, h => by
    cases h
    exact .refl _
  | n + 1, b, h => by
    rw [Function.iterate_succ_apply'] at h
    cases hn : (flip bind f)^[n] (some a) with
    | none =>
      rw [hn] at h
      cases h
    | some c =>
      rw [hn] at h
      exact (relatesInSteps_of_iterate hn).tail _ _ _ _ h

/-- The iterates of `c.machine` are those of `c.finMachine`, read through `symVal`. -/
private theorem iterate_step_finMachine (c : Code) :
    ∀ (n : ℕ) (d : TM0.Cfg (Fin c.symBound) ℕ),
      (flip bind (TM0.step c.machine))^[n] (some (d.map c.symVal id)) =
        ((flip bind (TM0.step c.finMachine))^[n] (some d)).map (TM0.Cfg.map c.symVal id)
  | 0, _ => rfl
  | n + 1, d => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    change (flip bind (TM0.step c.machine))^[n] (TM0.step c.machine (d.map c.symVal id)) =
      ((flip bind (TM0.step c.finMachine))^[n] (TM0.step c.finMachine d)).map _
    rw [step_finMachine]
    cases TM0.step c.finMachine d with
    | none =>
      change (flip bind (TM0.step c.machine))^[n] none =
        ((flip bind (TM0.step c.finMachine))^[n] none).map _
      rw [MetaMathlibExt.TM2Recursive.iterate_none_eq,
        MetaMathlibExt.TM2Recursive.iterate_none_eq]
      rfl
    | some d' => exact iterate_step_finMachine c n d'

/-- **The single-tape machine of a code runs it step for step.** If `c` has halted on `x` within
`T` steps, its single-tape machine halts on the input word of `x` within `T + 1` steps, the last
step entering its halting state, with a tape that reads as the tape of `c` after `T` steps. -/
theorem exists_relatesWithinSteps_singleTapeTM {c : Code} {x : List Bool} {T : ℕ}
    (h : c.step (c.cfgAfter x T) = none) :
    ∃ tape : BiTape (NonBlank (Fin c.symBound)),
      RelatesWithinSteps c.singleTapeTM.TransitionRelation
        (c.singleTapeTM.initCfg (x.map c.inputSym)) ⟨none, tape⟩ (T + 1) ∧
      (toTape tape).map c.symVal = (c.cfgAfter x T).toTM0.Tape := by
  obtain ⟨j, hj, hk⟩ := exists_iterate_eq_cfgAfter c x T
  set l₀ := (x.map c.inputSym).map Subtype.val
  have hinit : (TM0.init l₀ : TM0.Cfg (Fin c.symBound) ℕ).map c.symVal id =
      TM0.init (input x) := by
    rw [← map_symVal_inputSym c x]
    exact TM0.map_init c.symVal (⟨id, rfl⟩ : PointedMap ℕ ℕ) l₀
  have hit := iterate_step_toTM0 c j (init x)
  rw [hk, init_toTM0, ← hinit, iterate_step_finMachine, Option.map_some] at hit
  obtain ⟨d', hd', hmap⟩ := Option.map_eq_some_iff.1 hit
  have hhalt : TM0.step c.finMachine d' = none := by
    have hs := step_finMachine c d'
    rw [hmap, step_toTM0, h, Option.map_none] at hs
    exact Option.map_eq_none_iff.1 hs.symm
  obtain ⟨hc', tape, htape, hrun⟩ :=
    SingleTapeTM.relatesInSteps_ofTM0 c.finMachine c.states c.supports_finMachine
      (relatesInSteps_of_iterate hd') c.supports_finMachine.1
      (t := BiTape.mk₁ (x.map c.inputSym)) (SingleTapeTM.toTape_mk₁ _)
  have hlast := SingleTapeTM.step_ofTM0_of_step_eq_none c.finMachine c.states
    c.supports_finMachine hc' (t := tape) (by rw [htape]; exact hhalt)
  refine ⟨tape, RelatesWithinSteps.mono (by omega : j + 1 ≤ T + 1)
    (RelatesWithinSteps.of_relatesInSteps (hrun.tail _ _ _ _ hlast)), ?_⟩
  rw [htape, ← hmap]
  rfl

/-- A list of blanks reads as the blank half-tape. -/
private theorem listBlank_mk_eq_nil {l : List ℕ} (h : ∀ a ∈ l, a = 0) :
    ListBlank.mk l = ListBlank.mk [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [h a List.mem_cons_self, ← ListBlank.cons_mk,
      ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]
    exact ListBlank.cons_head_tail (ListBlank.mk [])

/-- A list that reads as the blank half-tape holds only blanks. -/
private theorem forall_eq_zero_of_listBlank_mk_eq_nil {l : List ℕ}
    (h : ListBlank.mk l = ListBlank.mk []) : ∀ a ∈ l, a = 0 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have := congrArg (fun L ↦ ListBlank.nth L i) h
  simp only [ListBlank.nth_mk, List.getI_nil] at this
  rwa [List.getI_eq_getElem _ hi] at this

/-- A configuration in the halting state reaches only itself. -/
private theorem eq_of_reflTransGen_of_state_eq_none {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : ReflTransGen tm.TransitionRelation a b) (ha : a.state = none) : a = b := by
  rcases h.cases_head with h | ⟨_, hs, -⟩
  · exact h
  · rw [SingleTapeTM.TransitionRelation, SingleTapeTM.step_eq_none_iff.2 ha] at hs
    cases hs

/-- Reading a half-tape of the single-tape machine of `c` through `symVal` is injective. -/
private theorem map_symVal_toListBlank_injective (c : Code) :
    Function.Injective fun s : StackTape (NonBlank (Fin c.symBound)) ↦
      (toListBlank s).map c.symVal := by
  intro s s' h
  refine SingleTapeTM.toListBlank_injective (ListBlank.ext fun i ↦ c.symVal_injective ?_)
  simp only at h
  rw [← ListBlank.nth_map, ← ListBlank.nth_map, h]

/-- **Deciding codes on single-tape machines.** If `c` decides `L` within `t`, then on the input
word of every `x` the single-tape machine of `c` halts within `t |x| + 1` steps, with the answer
symbol `c.inputSym (L x)` under the head and every cell right of the head blank. The cells left of
the head read as the cells left of the head of `c` after `t |x|` steps. -/
theorem DecidesWithin.exists_relatesWithinSteps_singleTapeTM {c : Code} {L : DecisionProblem}
    {t : ℕ → ℕ} (h : c.DecidesWithin L t) (x : List Bool) :
    ∃ left : StackTape (NonBlank (Fin c.symBound)),
      (toListBlank left).map c.symVal = ListBlank.mk (c.cfgAfter x (t x.length)).left ∧
      RelatesWithinSteps c.singleTapeTM.TransitionRelation
        (c.singleTapeTM.initCfg (x.map c.inputSym))
        ⟨none, ⟨some (c.inputSym (L x)), left, ∅⟩⟩ (t x.length + 1) := by
  obtain ⟨hs, hout⟩ := (evalSteps_eq_some_iff_output c x _ _).1 (h x)
  obtain ⟨⟨head, left, right⟩, hrun, htape⟩ := Code.exists_relatesWithinSteps_singleTapeTM hs
  have hr₀ := right₀_toTM0 (c.cfgAfter x (t x.length))
  rw [hout, ← htape] at hr₀
  have hhead := congrArg ListBlank.head hr₀
  have hright := congrArg ListBlank.tail hr₀
  simp only [Tape.right₀, ListBlank.head_cons, ListBlank.tail_cons] at hhead hright
  have hhead' : head = some (c.inputSym (L x)) := by
    cases head with
    | none => exact absurd hhead (by cases L x <;> simp [bitSym])
    | some s =>
      refine congrArg some (Subtype.ext (Fin.ext ?_))
      simpa using hhead
  have hright' : right = ∅ := by
    refine map_symVal_toListBlank_injective c (hright.trans ?_)
    change _ = (toListBlank StackTape.nil).map c.symVal
    rw [SingleTapeTM.toListBlank_nil, ListBlank.map_mk, ListBlank.tail_mk]
    rfl
  refine ⟨left, congrArg Tape.left htape, ?_⟩
  rw [hhead', hright'] at hrun
  exact hrun

/-- **CSLib's output convention.** If `c` decides `L` within `t` and every cell left of the head
of `c` is blank after `t |x|` steps on `x`, then the single-tape machine of `c` outputs
`[c.inputSym (L x)]` on the input word of `x` within `t |x| + 1` steps. -/
theorem DecidesWithin.outputsWithinTime_singleTapeTM {c : Code} {L : DecisionProblem}
    {t : ℕ → ℕ} (h : c.DecidesWithin L t) {x : List Bool}
    (hx : ∀ a ∈ (c.cfgAfter x (t x.length)).left, a = 0) :
    c.singleTapeTM.OutputsWithinTime (x.map c.inputSym) [c.inputSym (L x)]
      (t x.length + 1) := by
  obtain ⟨left, hleft, hrun⟩ := h.exists_relatesWithinSteps_singleTapeTM x
  rw [listBlank_mk_eq_nil hx] at hleft
  obtain rfl : left = ∅ := map_symVal_toListBlank_injective c hleft
  exact hrun

/-- **Exactly when CSLib's output convention holds.** If `c` decides `L` within `t`, the
single-tape machine of `c` outputs `[c.inputSym (L x)]` on the input word of `x`, after some
finite number of steps, if and only if every cell left of the head of `c` is blank after `t |x|`
steps on `x`. -/
theorem DecidesWithin.outputs_singleTapeTM_iff {c : Code} {L : DecisionProblem} {t : ℕ → ℕ}
    (h : c.DecidesWithin L t) (x : List Bool) :
    c.singleTapeTM.Outputs (x.map c.inputSym) [c.inputSym (L x)] ↔
      ∀ a ∈ (c.cfgAfter x (t x.length)).left, a = 0 := by
  refine ⟨fun hout ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨left, hleft, m, -, hrun⟩ := h.exists_relatesWithinSteps_singleTapeTM x
    have hcfg : (⟨none, ⟨some (c.inputSym (L x)), left, ∅⟩⟩ : c.singleTapeTM.Cfg) =
        c.singleTapeTM.haltCfg [c.inputSym (L x)] := by
      rcases hrun.reflTransGen.total_of_right_unique c.singleTapeTM.rightUnique_transitionRelation
        hout with h' | h'
      · exact eq_of_reflTransGen_of_state_eq_none h' rfl
      · exact (eq_of_reflTransGen_of_state_eq_none h' rfl).symm
    have hl : left = ∅ := congrArg (fun C : c.singleTapeTM.Cfg ↦ C.BiTape.left) hcfg
    subst hl
    refine forall_eq_zero_of_listBlank_mk_eq_nil (hleft.symm.trans ?_)
    change (toListBlank StackTape.nil).map c.symVal = _
    rw [SingleTapeTM.toListBlank_nil, ListBlank.map_mk]
    rfl
  · obtain ⟨m, -, hrun⟩ := h.outputsWithinTime_singleTapeTM hx
    exact hrun.reflTransGen

end Code

end Cslib.Turing.Universal
