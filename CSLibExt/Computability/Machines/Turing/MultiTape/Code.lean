/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic
public import Mathlib.Computability.Primrec.List

/-!
# Codes for multi-tape machines and their clocked evaluator

A `Code k` is a finite transition table for a machine of CSLib's multi-tape model
(`Turing.MultiTapeTM k Bool ℕ`: a read-only binary input tape, `k` work tapes, a write-only output
tape) whose states are numbers. Each entry maps a key `(q, a, w)`, a state together with the
symbols under the input head and the `k` work heads (`none` is the blank), to a `CodeAction`;
the first matching entry wins, and a missing key halts the machine without moving or writing.
Head moves are coded as numbers: `0` moves left, `1` stays, anything else moves right
(`decodeMove`). State `0` is the initial state. `Code.toTM c` is the decoded machine; it is built
with `MultiTapeTM.ofTr`, so it is a machine of CSLib's model and every upstream notion (runs,
halting, `Computes`, `RunsInTime`, `RunsInSpace`) applies to it unchanged.

Codes are `Primcodable` (as lists of tuples), so `Code.encode` and `Code.decode` code them by
natural numbers with `decode (encode c) = some c`.

`Code.evalSteps c x T` runs `c` on the input `x` for `T` steps on explicit, finitary
configurations (`Code.Config`: work tapes as zippers, no head positions) and returns
`some output` when the machine has halted, `none` otherwise. A simulation relation
(`Code.Represents`) ties these configurations to CSLib's `Turing.Cfg`, step for step
(`Code.Represents.step`), so the evaluator agrees with the upstream semantics
(`Code.evalSteps_eq_some_iff`, `Code.computes_iff_exists_evalSteps`), and it is primitive
recursive in the code, the input and the clock (`Code.primrec_evalSteps`).

This is the interface a universal machine needs: a code type, a clocked evaluator, and its
agreement with the machine semantics. That codes cover exactly the finite-state binary machines
is in `MultiTape/CodeCompleteness.lean`; a universal *machine* is not built here
(`CSLibExt/BACKLOG.md`, MT3).

## Main definitions

- `Cslib.Turing.MultiTapeTM.Code`, `Code.toTM`: codes and the machines they denote.
- `Cslib.Turing.MultiTapeTM.Code.encode`, `Code.decode`: coding by natural numbers.
- `Cslib.Turing.MultiTapeTM.Code.states`: the finite set of states of a code.
- `Cslib.Turing.MultiTapeTM.Code.Config`, `Code.Config.step`, `Code.evalSteps`: the clocked
  evaluator.

## Main results

- `Code.decode_encode`: codes round-trip through `ℕ`.
- `Code.state_runFrom_mem_states`: every state a run of `c.toTM` enters lies in `c.states`.
- `Code.represents_iterate`: the evaluator's configuration after `t` steps represents the
  configuration of `c.toTM` after `t` steps.
- `Code.evalSteps_eq_some_iff`, `Code.isSome_evalSteps_iff_runsInTime`, `Code.evalSteps_mono`,
  `Code.computes_iff_exists_evalSteps`: agreement with CSLib's semantics.
- `Code.primrec_evalSteps`: the evaluator is primitive recursive.

## References

- C. Papadimitriou, *Computational Complexity*, §2.3 (the multi-tape model; CSLib's definition is
  adapted from it).
- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., §9.1 (codes and clocked
  simulation in the hierarchy theorems).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ}

/-! ### Actions and codes -/

/-- Decode a head move: `0` moves left, `1` stays, anything else moves right. -/
def decodeMove (m : ℕ) : SignType :=
  if m = 0 then -1 else if m = 1 then 0 else 1

/-- A coded action: the input-head move, for every work tape an optional symbol to write
(`some none` writes a blank) and a head move, an optional output bit, and the next state (`none`
halts). Moves are coded as in `decodeMove`. -/
structure CodeAction (k : ℕ) where
  /-- The coded input-head move. -/
  inputMove : ℕ
  /-- For each work tape: an optional symbol to write and the coded head move. -/
  work : Fin k → Option (Option Bool) × ℕ
  /-- An optional output bit. -/
  out : Option Bool
  /-- The next state, `none` to halt. -/
  next : Option ℕ

namespace CodeAction

/-- Coded actions are tuples. -/
def equivProd :
    CodeAction k ≃ ℕ × (Fin k → Option (Option Bool) × ℕ) × Option Bool × Option ℕ where
  toFun a := (a.inputMove, a.work, a.out, a.next)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (CodeAction k) := Primcodable.ofEquiv _ equivProd

/-- The action of CSLib's model that a coded action stands for. -/
def toAction (a : CodeAction k) : Action k Bool ℕ where
  inputTape := decodeMove a.inputMove
  workTapes i := ((a.work i).1, decodeMove (a.work i).2)
  output := a.out
  state := a.next

/-- The default action of a missing table entry: halt without moving, writing or emitting. -/
def halt : CodeAction k := ⟨1, fun _ ↦ (none, 1), none, none⟩

end CodeAction

/-- The key of a table entry: a state, the symbol under the input head and the symbols under the
work heads. -/
abbrev CodeKey (k : ℕ) := ℕ × Option Bool × (Fin k → Option Bool)

/-- A code for a multi-tape machine over the binary alphabet with states in `ℕ`: a finite list of
table entries, looked up by key (the first match wins); a missing key halts. -/
structure Code (k : ℕ) where
  /-- The table entries. -/
  table : List (CodeKey k × CodeAction k)

namespace Code

/-- Codes are their tables. -/
def equivTable : Code k ≃ List (CodeKey k × CodeAction k) where
  toFun := table
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (Code k) := Primcodable.ofEquiv _ equivTable

/-- The number coding a code. -/
def encode (c : Code k) : ℕ := Encodable.encode c

/-- The code coded by a number, if any. -/
def decode (n : ℕ) : Option (Code k) := Encodable.decode n

/-- **Code round-trip.** -/
@[simp]
theorem decode_encode (c : Code k) : decode (encode c) = some c :=
  Encodable.encodek c

/-- The coding of codes is injective. -/
theorem encode_injective : Function.Injective (encode (k := k)) :=
  Encodable.encode_injective

/-- The coded action of a code at a state and the symbols under the heads. -/
def act (c : Code k) (q : ℕ) (a : Option Bool) (w : Fin k → Option Bool) : CodeAction k :=
  ((@List.lookup _ _ instBEqOfDecidableEq (q, a, w) c.table)).getD CodeAction.halt

/-- The transition function of a code. -/
def tr (c : Code k) (q : ℕ) (a : Option Bool) (w : Fin k → Option Bool) : Action k Bool ℕ :=
  (c.act q a w).toAction

/-- The machine of a code, a machine of CSLib's multi-tape model; it starts in state `0`. -/
noncomputable def toTM (c : Code k) : MultiTapeTM k Bool ℕ := MultiTapeTM.ofTr 0 c.tr

@[simp]
theorem q₀_toTM (c : Code k) : c.toTM.q₀ = 0 := rfl

/-- The step of the machine of a code. -/
theorem step_toTM (c : Code k) {x : List Bool} (cfg : Cfg k Bool ℕ x) :
    c.toTM.step cfg = stepWith c.tr cfg :=
  step_ofTr 0 c.tr cfg

/-! ### Finitely many states -/

/-- The states of a code: the initial state and every state its table enters. -/
def states (c : Code k) : Finset ℕ :=
  insert 0 (c.table.filterMap fun e ↦ e.2.next).toFinset

private theorem mem_of_lookup_eq_some {κ β : Type*} [DecidableEq κ] :
    ∀ {l : List (κ × β)} {a : κ} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: l, a, b, h => by
    by_cases ha : a = a'
    · subst ha
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have : (a == a') = false := by simpa using ha
      rw [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

/-- The next state of every action of a code is a state of the code. -/
theorem next_act_mem_states (c : Code k) {q q' : ℕ} {a : Option Bool} {w : Fin k → Option Bool}
    (h : (c.act q a w).next = some q') : q' ∈ c.states := by
  unfold act at h
  cases hl : @List.lookup _ _ instBEqOfDecidableEq (q, a, w) c.table with
  | none => simp [hl, CodeAction.halt] at h
  | some e =>
    rw [hl, Option.getD_some] at h
    refine Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_filterMap.mpr ?_))
    exact ⟨_, mem_of_lookup_eq_some hl, h⟩

/-- **Codes denote finite-state machines.** Every state that a run of the machine of a code
enters from the initial configuration lies in the finite set `c.states`. -/
theorem state_runFrom_mem_states (c : Code k) (x : List Bool) (t : ℕ) {q : ℕ}
    (h : (c.toTM.runFrom (c.toTM.initCfg x) t).state = some q) : q ∈ c.states := by
  induction t generalizing q with
  | zero => simp only [runFrom_zero, MultiTapeNTM.initCfg, Cfg.init] at h; cases h; simp [states]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ, step_toTM] at h
    revert h
    unfold stepWith
    split
    · exact ih
    · intro h
      exact c.next_act_mem_states h

/-! ### Finitary configurations -/

/-- A work tape as a zipper: the cells left of the head, nearest first, and the cells from the
head rightwards; cells beyond both lists are blank. -/
abbrev Tape := List (Option Bool) × List (Option Bool)

namespace Tape

/-- The symbol under the head. -/
def read (t : Tape) : Option Bool := t.2.headI

/-- Optionally write a symbol under the head. -/
def write : Option (Option Bool) → Tape → Tape
  | none, t => t
  | some s, t => (t.1, s :: t.2.tail)

/-- Move the head by a coded move (as in `decodeMove`). -/
def move (m : ℕ) (t : Tape) : Tape :=
  if m = 0 then (t.1.tail, t.1.headI :: t.2)
  else if m = 1 then t
  else (t.2.headI :: t.1, t.2.tail)

/-- The cell at offset `j` from the head. -/
def cell (t : Tape) : ℤ → Option Bool
  | .ofNat n => t.2.getD n none
  | .negSucc n => t.1.getD n none

theorem read_eq_cell_zero (t : Tape) : t.read = t.cell 0 := by
  rcases t with ⟨l, r⟩
  cases r <;> rfl

private theorem getD_tail (l : List (Option Bool)) (n : ℕ) :
    l.tail.getD n none = l.getD (n + 1) none := by
  cases l <;> simp

theorem cell_write (w : Option (Option Bool)) (t : Tape) (j : ℤ) :
    (write w t).cell j = match w with
      | none => t.cell j
      | some s => if j = 0 then s else t.cell j := by
  rcases t with ⟨l, r⟩
  cases w with
  | none => rfl
  | some s =>
    rcases j with n | n
    · cases n with
      | zero => rfl
      | succ n =>
        have hn : (Int.ofNat (n + 1)) ≠ 0 := by simp only [ne_eq, Int.ofNat_eq_natCast]; omega
        simp only [write, cell, hn, ↓reduceIte]
        simp
    · simp [write, cell]

theorem cell_move (m : ℕ) (t : Tape) (j : ℤ) :
    (move m t).cell j = t.cell (j + (decodeMove m : ℤ)) := by
  rcases t with ⟨l, r⟩
  unfold move decodeMove
  split_ifs with h0 h1
  · -- left: the new tape at `j` is the old tape at `j - 1`
    rcases j with n | n
    · cases n with
      | zero => cases l <;> rfl
      | succ n =>
        simp only [cell, Int.ofNat_eq_natCast, SignType.coe_neg, SignType.coe_one]
        rw [show ((n + 1 : ℕ) : ℤ) + -1 = ((n : ℕ) : ℤ) by omega]
        simp
    · simp only [cell, SignType.coe_neg, SignType.coe_one]
      rw [show Int.negSucc n + -1 = Int.negSucc (n + 1) by omega]
      simp
  · simp
  · rcases j with n | n
    · simp only [cell, Int.ofNat_eq_natCast, SignType.coe_one]
      rw [show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
      simp
    · cases n with
      | zero =>
        simp only [cell, SignType.coe_one]
        rw [show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) by omega]
        cases r <;> rfl
      | succ n =>
        simp only [cell, SignType.coe_one]
        rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega]
        simp

end Tape

/-- An explicit configuration: the state (`none` when halted), the input head position (shifted
by one, as in `Turing.Cfg`), the work tapes as zippers, and the output so far. -/
structure Config (k : ℕ) where
  /-- The state, `none` when halted. -/
  state : Option ℕ
  /-- The input head position, shifted by one. -/
  inputPos : ℕ
  /-- The work tapes. -/
  tapes : Fin k → Tape
  /-- The output so far. -/
  output : List Bool

namespace Config

/-- Explicit configurations are tuples. -/
def equivProd : Config k ≃ Option ℕ × ℕ × (Fin k → Tape) × List Bool where
  toFun e := (e.state, e.inputPos, e.tapes, e.output)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (Config k) := Primcodable.ofEquiv _ equivProd

/-- The initial configuration: state `0`, the input head on the first input cell, blank work
tapes, empty output. -/
def init : Config k := ⟨some 0, 1, fun _ ↦ ([], []), []⟩

/-- The input symbol at a (shifted) input head position. -/
def inputSym (x : List Bool) (p : ℕ) : Option Bool := if p = 0 then none else x[p - 1]?

/-- Move the input head by a coded move, staying within one cell of the input. -/
def moveInput (n p m : ℕ) : ℕ := if m = 0 then p - 1 else if m = 1 then p else min (p + 1) (n + 1)

/-- Apply a coded action. -/
def apply (x : List Bool) (a : CodeAction k) (e : Config k) : Config k where
  state := a.next
  inputPos := moveInput x.length e.inputPos a.inputMove
  tapes i := Tape.move (a.work i).2 (Tape.write (a.work i).1 (e.tapes i))
  output := e.output ++ a.out.toList

/-- One step of the evaluator for the code `c` on the input `x`. -/
def step (c : Code k) (x : List Bool) (e : Config k) : Config k :=
  match e.state with
  | none => e
  | some q => e.apply x (c.act q (inputSym x e.inputPos) fun i ↦ (e.tapes i).read)

end Config

/-- The clocked evaluator: run `c` on `x` for `T` steps; `some output` if the machine has halted
by then, `none` otherwise. -/
def evalSteps (c : Code k) (x : List Bool) (T : ℕ) : Option (List Bool) :=
  match ((Config.step c x)^[T] Config.init).state with
  | none => some ((Config.step c x)^[T] Config.init).output
  | some _ => none

/-! ### Agreement with CSLib's semantics -/

/-- The explicit configuration `e` represents the configuration `cfg` of CSLib's model on input
`x`: same state, input head and output, and each work tape of `e` read from the head is the
corresponding work tape of `cfg` read from its head position. -/
structure Represents {x : List Bool} (e : Config k) (cfg : Cfg k Bool ℕ x) : Prop where
  state : e.state = cfg.state
  inputPos : e.inputPos = cfg.inputPos.val
  output : e.output = cfg.output
  tapes : ∀ i z, cfg.workTapes i z = (e.tapes i).cell (z - cfg.workTapePos i)

theorem represents_init (c : Code k) (x : List Bool) :
    Represents (Config.init (k := k)) (c.toTM.initCfg x) where
  state := rfl
  inputPos := rfl
  output := rfl
  tapes i z := by
    simp only [MultiTapeNTM.initCfg, Cfg.init, q₀_toTM, Config.init]
    rcases (z - 0) with n | n <;> simp [Tape.cell]

private theorem inputSymbol_eq {x : List Bool} {e : Config k} {cfg : Cfg k Bool ℕ x}
    (h : Represents e cfg) : cfg.inputSymbol = Config.inputSym x e.inputPos := by
  rw [h.inputPos]
  unfold Config.inputSym
  have hlt := cfg.inputPos.isLt
  by_cases h0 : cfg.inputPos.val = 0
  · rw [inputSymbol_eq_none_of_boundary (Or.inl h0)]
    simp [h0]
  · by_cases h1 : cfg.inputPos.val = x.length + 1
    · rw [inputSymbol_eq_none_of_boundary (Or.inr h1)]
      simp [h1]
    · rw [inputSymbolInner (cfg.inputPos.val - 1) (by omega) (by omega)]
      simp only [h0, ↓reduceIte]
      rw [List.getElem?_eq_getElem (by omega)]

private theorem moveInput_eq {n : ℕ} (p : Fin (n + 2)) (m : ℕ) :
    Config.moveInput n p.val m = (moveInputPos p (decodeMove m)).val := by
  have hv := val_moveInputPos_eq p (decodeMove m)
  have hlt := p.isLt
  unfold Config.moveInput
  by_cases h0 : m = 0
  · subst h0
    have hd : decodeMove 0 = -1 := by simp [decodeMove]
    rw [hd] at hv ⊢
    rw [SignType.coe_neg_one] at hv
    simp only [↓reduceIte]
    rw [max_def, min_def] at hv
    split_ifs at hv <;> omega
  · by_cases h1 : m = 1
    · subst h1
      have hd : decodeMove 1 = 0 := by simp [decodeMove]
      rw [hd] at hv ⊢
      rw [SignType.coe_zero] at hv
      simp only [one_ne_zero, ↓reduceIte]
      rw [max_def, min_def] at hv
      split_ifs at hv <;> omega
    · have hd : decodeMove m = 1 := by simp [decodeMove, h0, h1]
      rw [hd] at hv ⊢
      rw [SignType.coe_one] at hv
      simp only [h0, h1, ↓reduceIte]
      rw [max_def, min_def] at hv
      split_ifs at hv <;> omega

/-- **The evaluator simulates the machine step for step.** -/
theorem Represents.step (c : Code k) {x : List Bool} {e : Config k} {cfg : Cfg k Bool ℕ x}
    (h : Represents e cfg) : Represents (Config.step c x e) (c.toTM.step cfg) := by
  rw [step_toTM]
  unfold Config.step stepWith
  rw [← h.state]
  cases hq : e.state with
  | none => exact h
  | some q =>
    simp only
    have hw : cfg.workTapeSymbols = fun i ↦ (e.tapes i).read := by
      funext i
      rw [Cfg.workTapeSymbols, h.tapes, sub_self, Tape.read_eq_cell_zero]
    rw [inputSymbol_eq h, hw]
    unfold tr
    generalize c.act q (Config.inputSym x e.inputPos) (fun i ↦ (e.tapes i).read) = a
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [Config.apply, CodeAction.toAction, Action.apply_inputPos]
      rw [h.inputPos]
      exact moveInput_eq cfg.inputPos a.inputMove
    · simp [Config.apply, Action.apply_output, h.output, CodeAction.toAction]
    · intro i z
      simp only [Config.apply, Action.apply_workTapes, Action.apply_workTapePos,
        CodeAction.toAction]
      rw [Tape.cell_move, Tape.cell_write]
      have hz : z - (cfg.workTapePos i + (decodeMove (a.work i).2 : ℤ)) +
          (decodeMove (a.work i).2 : ℤ) = z - cfg.workTapePos i := by omega
      rw [hz]
      cases (a.work i).1 with
      | none => exact h.tapes i z
      | some s =>
        simp only
        by_cases hzp : z = cfg.workTapePos i
        · subst hzp
          simp
        · simp only [Function.update_of_ne hzp, sub_ne_zero.mpr hzp, ↓reduceIte]
          exact h.tapes i z

/-- The evaluator's configuration after `t` steps represents the machine's. -/
theorem represents_iterate (c : Code k) (x : List Bool) (t : ℕ) :
    Represents ((Config.step c x)^[t] Config.init) (c.toTM.runFrom (c.toTM.initCfg x) t) := by
  induction t with
  | zero => exact represents_init c x
  | succ t ih =>
    rw [Function.iterate_succ_apply', MultiTapeTM.runFrom_succ]
    exact ih.step c

/-- **Evaluator agreement.** `evalSteps c x T` returns `o` iff the machine of `c` has halted
after `T` steps on `x`, with output `o`. -/
theorem evalSteps_eq_some_iff (c : Code k) (x : List Bool) (T : ℕ) (o : List Bool) :
    c.evalSteps x T = some o ↔
      (c.toTM.runFrom (c.toTM.initCfg x) T).Halted ∧
        (c.toTM.runFrom (c.toTM.initCfg x) T).output = o := by
  have h := represents_iterate c x T
  unfold evalSteps
  simp only [Cfg.Halted, ← h.state, ← h.output]
  cases ((Config.step c x)^[T] Config.init).state <;> simp

/-- `evalSteps c x T` is defined iff the machine of `c` runs in time `T` on `x`. -/
theorem isSome_evalSteps_iff_runsInTime (c : Code k) (x : List Bool) (T : ℕ) :
    (c.evalSteps x T).isSome ↔ c.toTM.RunsInTime x T := by
  rw [runsInTime_iff_halted, Option.isSome_iff_exists]
  simp only [evalSteps_eq_some_iff]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨_, h, rfl⟩⟩

/-- A result within `T` steps stays the result for every larger clock. -/
theorem evalSteps_mono (c : Code k) {x : List Bool} {T T' : ℕ} {o : List Bool}
    (h : c.evalSteps x T = some o) (hT : T ≤ T') : c.evalSteps x T' = some o := by
  rw [evalSteps_eq_some_iff] at h ⊢
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ hT h.1]
  exact h

/-- The machine of `c` computes `o` on `x` iff some clock makes the evaluator return `o`. -/
theorem computes_iff_exists_evalSteps (c : Code k) (x o : List Bool) :
    c.toTM.Computes x o ↔ ∃ T, c.evalSteps x T = some o := by
  simp only [evalSteps_eq_some_iff]
  rfl

/-! ### Primitive recursiveness -/

section Primrec

private theorem primrec_finArrow {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → Fin k → σ} (hf : ∀ i, Primrec fun a ↦ f a i) : Primrec f :=
  (Primrec.vector_get'.comp (Primrec.vector_ofFn hf)).of_eq fun a ↦ by funext i; simp

private theorem primrec_table : Primrec (Code.table (k := k)) :=
  Primrec.of_equiv (e := equivTable)

private theorem primrec_inputMove : Primrec (CodeAction.inputMove (k := k)) :=
  Primrec.fst.comp (Primrec.of_equiv (e := CodeAction.equivProd))

private theorem primrec_work : Primrec (CodeAction.work (k := k)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := CodeAction.equivProd)))

private theorem primrec_out : Primrec (CodeAction.out (k := k)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := CodeAction.equivProd))))

private theorem primrec_next : Primrec (CodeAction.next (k := k)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := CodeAction.equivProd))))

private theorem primrec_cfg_state : Primrec (Config.state (k := k)) :=
  Primrec.fst.comp (Primrec.of_equiv (e := Config.equivProd))

private theorem primrec_cfg_inputPos : Primrec (Config.inputPos (k := k)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Config.equivProd)))

private theorem primrec_cfg_tapes : Primrec (Config.tapes (k := k)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Config.equivProd))))

private theorem primrec_cfg_output : Primrec (Config.output (k := k)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Config.equivProd))))

private theorem primrec_cfg_mk {α : Type*} [Primcodable α] {f₁ : α → Option ℕ} {f₂ : α → ℕ}
    {f₃ : α → Fin k → Tape} {f₄ : α → List Bool} (h₁ : Primrec f₁) (h₂ : Primrec f₂)
    (h₃ : Primrec f₃) (h₄ : Primrec f₄) :
    Primrec fun a ↦ (Config.mk (f₁ a) (f₂ a) (f₃ a) (f₄ a) : Config k) :=
  (Primrec.of_equiv_symm (e := Config.equivProd)).comp (h₁.pair (h₂.pair (h₃.pair h₄)))

private theorem primrec_read : Primrec Tape.read :=
  Primrec.list_headI.comp Primrec.snd

private theorem primrec_write : Primrec₂ Tape.write := by
  refine (Primrec.option_casesOn Primrec.fst Primrec.snd
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂).of_eq
    fun p ↦ ?_
  rcases p with ⟨_ | _, _⟩ <;> rfl

private theorem primrec_move : Primrec₂ Tape.move := by
  have ht : Primrec fun p : ℕ × Tape ↦ p.2 := Primrec.snd
  refine (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    ((Primrec.list_tail.comp (Primrec.fst.comp ht)).pair
      (Primrec.list_cons.comp (Primrec.list_headI.comp (Primrec.fst.comp ht))
        (Primrec.snd.comp ht)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) ht
      ((Primrec.list_cons.comp (Primrec.list_headI.comp (Primrec.snd.comp ht))
        (Primrec.fst.comp ht)).pair (Primrec.list_tail.comp (Primrec.snd.comp ht))))).of_eq
    fun p ↦ ?_
  rfl

private theorem primrec_inputSym : Primrec₂ Config.inputSym :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

private theorem primrec_moveInput :
    Primrec fun p : ℕ × ℕ × ℕ ↦ Config.moveInput p.1 p.2.1 p.2.2 := by
  have hn : Primrec fun p : ℕ × ℕ × ℕ ↦ p.1 := Primrec.fst
  have hp : Primrec fun p : ℕ × ℕ × ℕ ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun p : ℕ × ℕ × ℕ ↦ p.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
    (Primrec.nat_sub.comp hp (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) hp
      (Primrec.nat_min.comp (Primrec.nat_add.comp hp (Primrec.const 1))
        (Primrec.nat_add.comp hn (Primrec.const 1))))

private theorem primrec_act :
    Primrec fun p : Code k × CodeKey k ↦ p.1.act p.2.1 p.2.2.1 p.2.2.2 := by
  refine (Primrec.option_getD.comp (Primrec.listLookup.comp Primrec.snd
    (primrec_table.comp Primrec.fst)) (Primrec.const CodeAction.halt)).of_eq fun p ↦ ?_
  rfl

private theorem primrec_apply :
    Primrec fun p : List Bool × CodeAction k × Config k ↦ p.2.2.apply p.1 p.2.1 := by
  have hx : Primrec fun p : List Bool × CodeAction k × Config k ↦ p.1 := Primrec.fst
  have ha : Primrec fun p : List Bool × CodeAction k × Config k ↦ p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have he : Primrec fun p : List Bool × CodeAction k × Config k ↦ p.2.2 :=
    Primrec.snd.comp Primrec.snd
  refine primrec_cfg_mk (primrec_next.comp ha)
    (primrec_moveInput.comp ((Primrec.list_length.comp hx).pair
      ((primrec_cfg_inputPos.comp he).pair (primrec_inputMove.comp ha))))
    (primrec_finArrow fun i ↦ ?_)
    (Primrec.list_append.comp (primrec_cfg_output.comp he)
      (Primrec.optionToList.comp (primrec_out.comp ha)))
  have hw : Primrec fun p : List Bool × CodeAction k × Config k ↦ p.2.1.work i :=
    Primrec.fin_app.comp (primrec_work.comp ha) (Primrec.const i)
  exact primrec_move.comp (Primrec.snd.comp hw)
    (primrec_write.comp (Primrec.fst.comp hw)
      (Primrec.fin_app.comp (primrec_cfg_tapes.comp he) (Primrec.const i)))

private theorem primrec_step :
    Primrec fun p : Code k × List Bool × Config k ↦ Config.step p.1 p.2.1 p.2.2 := by
  have hc : Primrec fun p : Code k × List Bool × Config k ↦ p.1 := Primrec.fst
  have hx : Primrec fun p : Code k × List Bool × Config k ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  have he : Primrec fun p : Code k × List Bool × Config k ↦ p.2.2 := Primrec.snd.comp Primrec.snd
  have hread : Primrec fun p : Code k × List Bool × Config k ↦ fun i ↦ (p.2.2.tapes i).read :=
    primrec_finArrow fun i ↦ primrec_read.comp
      (Primrec.fin_app.comp (primrec_cfg_tapes.comp he) (Primrec.const i))
  have hact : Primrec₂ fun (p : Code k × List Bool × Config k) (q : ℕ) ↦
      p.1.act q (Config.inputSym p.2.1 p.2.2.inputPos) fun i ↦ (p.2.2.tapes i).read :=
    primrec_act.comp ((hc.comp Primrec.fst).pair (Primrec.snd.pair
      ((primrec_inputSym.comp (hx.comp Primrec.fst) (primrec_cfg_inputPos.comp
        (he.comp Primrec.fst))).pair (hread.comp Primrec.fst))))
  refine (Primrec.option_casesOn (primrec_cfg_state.comp he) he
    (primrec_apply.comp ((hx.comp Primrec.fst).pair
      ((hact.comp Primrec.fst Primrec.snd).pair (he.comp Primrec.fst)))).to₂).of_eq
    fun p ↦ ?_
  unfold Config.step
  cases p.2.2.state <;> rfl

/-- **The evaluator is primitive recursive** in the code, the input and the clock. -/
theorem primrec_evalSteps :
    Primrec fun p : Code k × List Bool × ℕ ↦ p.1.evalSteps p.2.1 p.2.2 := by
  have hit : Primrec fun p : Code k × List Bool × ℕ ↦
      (Config.step p.1 p.2.1)^[p.2.2] (Config.init (k := k)) :=
    Primrec.nat_iterate (Primrec.snd.comp Primrec.snd) (Primrec.const _)
      (primrec_step.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂
  refine (Primrec.option_casesOn (primrec_cfg_state.comp hit)
    (Primrec.option_some.comp (primrec_cfg_output.comp hit)) (Primrec.const none).to₂).of_eq
    fun p ↦ ?_
  unfold evalSteps
  cases ((Config.step p.1 p.2.1)^[p.2.2] Config.init).state <;> rfl

end Primrec

end Code

end Cslib.Turing.MultiTapeTM
