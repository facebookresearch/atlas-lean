/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.DropRight
public import MathlibExt.Computability.TuringMachine.Recursive.Halts

/-!
# Codes for single-tape machines and their clocked semantics

A `Code` is the transition table of a single-tape machine (Mathlib's `Turing.TM0`) whose states
and symbols are numbers: row `q`, column `a` of the table holds `none` (halt) or `some (q', s)`,
where `s` codes an action (`0` moves left, `1` moves right, `a' + 2` writes `a'`). State `0` is the
initial state and symbol `0` the blank; a state or symbol outside the table halts the machine.
`Code.machine c` is the decoded `TM0.Machine ℕ ℕ`, and input bits are written as the symbols `1`
(`false`) and `2` (`true`).

`Code.evalSteps c x T` runs `c` on the bits `x` for at most `T` steps. It returns
`some (output)` when the machine halts within `T` steps, the output being the tape from the head
rightwards with its trailing blanks dropped (the canonical representative of `TM0.eval`'s answer),
and `none` otherwise. The simulation runs on explicit configurations `Code.Cfg`, which read as
Mathlib configurations step for step (`Code.step_toTM0`).

This is the interface of a universal machine with a clock: a code type, a clocked evaluator and
its agreement with the unclocked semantics. It is meant to be bridged to CSLib's planned universal
machine (leanprover/cslib#611, on CSLib's own machine types) once that exists, not to replace it.
Codes denote Mathlib `TM0` machines; CSLib's single-tape machines are reached from `TM0` machines
(`SingleTapeTM.ofTM0`), not the other way round, so `exists_code` does not yet cover them.

## Main definitions

- `Cslib.Turing.Universal.Code`, `Code.machine`: codes and the machines they denote.
- `Cslib.Turing.Universal.HaltsWithin M l T`: started on `l`, the `TM0` machine `M` reaches a
  configuration without a successor within `T` steps.
- `Cslib.Turing.Universal.Code.evalSteps`: the clocked evaluator.

## Main results

- `Code.supports_machine`: the machine of a code is supported by a finite set of states.
- `Code.evalSteps_mono`: a result within `T` steps stays the result for every larger clock.
- `Code.isSome_evalSteps_iff`: `evalSteps c x T` is defined iff `c.machine` halts on `x` within
  `T` steps.
- `Code.eval_eq_some_of_evalSteps_eq_some`: a result of `evalSteps` is the value of `TM0.eval`.
- `Code.dom_eval_iff_exists_isSome_evalSteps`: `TM0.eval` is defined iff some clock suffices.
- `Code.exists_code`: every `TM0` machine with a finite alphabet, a finite supporting set of
  states (`TM0.Supports`) and two distinct non-blank input symbols `ι false`, `ι true` (so the
  alphabet has at least three symbols) has a code that simulates it step for step, up to an
  injective relabelling of the symbols that sends the input symbols to `1` and `2`.
- `Code.primrec_evalSteps`: `evalSteps` is primitive recursive in the code, the input and the
  clock.

## References

- J. Hartmanis and R. E. Stearns, *On the computational complexity of algorithms*, Trans. AMS 117
  (1965), 285–306.
- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Section 9.1.
-/

@[expose] public section

set_option autoImplicit false

open _root_.Turing StateTransition

namespace Cslib.Turing.Universal

/-! ### Halting within a number of steps -/

section HaltsWithin

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- `HaltsWithin M l T`: started on `l`, the `TM0` machine `M` reaches a configuration without a
successor after at most `T` steps. -/
def HaltsWithin (M : TM0.Machine Γ Λ) (l : List Γ) (T : ℕ) : Prop :=
  ∃ j ≤ T, ∃ d, (flip bind (TM0.step M))^[j] (some (TM0.init l)) = some d ∧ TM0.step M d = none

/-- `HaltsWithin` is monotone in the number of steps. -/
theorem HaltsWithin.mono {M : TM0.Machine Γ Λ} {l : List Γ} {T T' : ℕ} (h : HaltsWithin M l T)
    (hT : T ≤ T') : HaltsWithin M l T' := by
  obtain ⟨j, hj, d, hd⟩ := h
  exact ⟨j, hj.trans hT, d, hd⟩

/-- A `TM0` machine halts iff it halts within some number of steps. -/
theorem dom_eval_iff_exists_haltsWithin (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ ∃ T, HaltsWithin M l T := by
  rw [TM0.eval, Part.map_Dom, MetaMathlibExt.TM2Recursive.dom_eval_iff_exists_iterate]
  exact ⟨fun ⟨j, d, hd⟩ ↦ ⟨j, j, le_rfl, d, hd⟩, fun ⟨_, j, _, d, hd⟩ ↦ ⟨j, d, hd⟩⟩

end HaltsWithin

/-! ### Codes -/

/-- A code for a single-tape machine with states and symbols in `ℕ`: row `q`, column `a` of
`table` is `none` (halt) or `some (q', s)` (enter `q'` and do the action coded by `s`, see
`decodeStmt`). Missing rows and columns halt. -/
structure Code where
  /-- The transition table, indexed by state, then by symbol. -/
  table : List (List (Option (ℕ × ℕ)))
  deriving DecidableEq

/-- Decode an action: `0` moves left, `1` moves right, `a + 2` writes `a`. -/
def decodeStmt : ℕ → TM0.Stmt ℕ
  | 0 => .move .left
  | 1 => .move .right
  | a + 2 => .write a

/-- The symbol of an input bit: `false` is `1` and `true` is `2`; `0` is the blank. -/
def bitSym (b : Bool) : ℕ := cond b 2 1

/-- The input word of the bits `x`. -/
def input (x : List Bool) : List ℕ := x.map bitSym

namespace Code

/-- Codes are their tables. -/
def equivTable : Code ≃ List (List (Option (ℕ × ℕ))) where
  toFun := table
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Codes are coded as their tables. -/
instance : Primcodable Code := Primcodable.ofEquiv _ equivTable

/-- The entry of the table at state `q` and symbol `a`, `none` outside the table. -/
def lookup (c : Code) (q a : ℕ) : Option (ℕ × ℕ) := (c.table[q]?.bind fun row ↦ row[a]?).join

/-- The `TM0` machine of a code. -/
def machine (c : Code) : TM0.Machine ℕ ℕ := fun q a ↦
  (c.lookup q a).map fun e ↦ (e.1, decodeStmt e.2)

/-- The states of a code: the initial state `0` and every state its table enters. -/
def states (c : Code) : Finset ℕ :=
  insert 0 (c.table.flatten.filterMap fun o ↦ o.map Prod.fst).toFinset

/-- **Codes denote finite machines.** The decoded machine is supported by the finite set of
states of its code. -/
theorem supports_machine (c : Code) : TM0.Supports c.machine ↑c.states := by
  refine ⟨Finset.mem_insert_self _ _, fun {q a q' s} h _ ↦ ?_⟩
  simp only [machine, lookup, Option.mem_def, Option.map_eq_some_iff, Option.join_eq_some_iff,
    Option.bind_eq_some_iff] at h
  obtain ⟨⟨q'', s'⟩, ⟨row, hrow, he⟩, hq⟩ := h
  cases hq
  simp only [states, Finset.coe_insert, List.coe_toFinset, Set.mem_insert_iff,
    List.mem_filterMap, List.mem_flatten]
  exact Or.inr ⟨_, ⟨row, List.mem_of_getElem? hrow, List.mem_of_getElem? he⟩, rfl⟩

/-! ### Explicit configurations -/

/-- A configuration of the simulation: the state, the cells left of the head (nearest first),
the cell under the head, and the cells right of the head (nearest first). -/
structure Cfg where
  /-- The state. -/
  q : ℕ
  /-- The cells left of the head, nearest first. -/
  left : List ℕ
  /-- The cell under the head. -/
  head : ℕ
  /-- The cells right of the head, nearest first. -/
  right : List ℕ
  deriving DecidableEq

/-- Configurations are tuples. -/
def Cfg.equivProd : Cfg ≃ ℕ × List ℕ × ℕ × List ℕ where
  toFun k := (k.q, k.left, k.head, k.right)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Configurations are coded as tuples. -/
instance : Primcodable Cfg := Primcodable.ofEquiv _ Cfg.equivProd

/-- The Mathlib configuration of an explicit configuration: lists are read with blanks beyond
their ends. -/
def Cfg.toTM0 (k : Cfg) : TM0.Cfg ℕ ℕ := ⟨k.q, ⟨k.head, ListBlank.mk k.left, ListBlank.mk k.right⟩⟩

/-- Enter the state `q'` and do the action coded by `s` (see `decodeStmt`). -/
def Cfg.act (k : Cfg) (q' : ℕ) : ℕ → Cfg
  | 0 => ⟨q', k.left.tail, k.left.headI, k.head :: k.right⟩
  | 1 => ⟨q', k.head :: k.left, k.right.headI, k.right.tail⟩
  | a + 2 => ⟨q', k.left, a, k.right⟩

/-- The output of a configuration: the tape from the head rightwards, without trailing blanks. -/
def Cfg.output (k : Cfg) : List ℕ := (k.head :: k.right).rdropWhile (· == 0)

/-- The initial configuration on the bits `x`. -/
def init (x : List Bool) : Cfg := ⟨0, [], (input x).headI, (input x).tail⟩

/-- One step of the simulation, `none` if the machine halts. -/
def step (c : Code) (k : Cfg) : Option Cfg := (c.lookup k.q k.head).map fun e ↦ k.act e.1 e.2

/-- One step of the simulation, or no change once the machine has halted. -/
def stepOrStay (c : Code) (k : Cfg) : Cfg := (c.step k).getD k

/-- The configuration after `T` steps on the bits `x`, or the halting configuration if the
machine halts earlier. -/
def cfgAfter (c : Code) (x : List Bool) (T : ℕ) : Cfg := c.stepOrStay^[T] (init x)

/-- **The clocked evaluator.** Run the code `c` on the bits `x` for at most `T` steps: the output
if it halts within `T` steps, `none` otherwise. -/
def evalSteps (c : Code) (x : List Bool) (T : ℕ) : Option (List ℕ) :=
  (c.step (c.cfgAfter x T)).elim (some (c.cfgAfter x T).output) fun _ ↦ none

/-! ### Agreement with Mathlib's semantics -/

/-- An explicit step reads as a step of the decoded machine. -/
theorem step_toTM0 (c : Code) (k : Cfg) :
    TM0.step c.machine k.toTM0 = (c.step k).map Cfg.toTM0 := by
  simp only [TM0.step, Cfg.toTM0, machine, step, Option.map_map]
  congr 1
  funext e
  obtain ⟨q', _ | _ | a⟩ := e <;>
    simp [decodeStmt, Cfg.act, Cfg.toTM0, Tape.move, Tape.write, ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]

/-- The initial configuration reads as Mathlib's. -/
theorem init_toTM0 (x : List Bool) : (init x).toTM0 = TM0.init (input x) := by
  cases h : input x with
  | nil => simp [init, Cfg.toTM0, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk', h]
  | cons a l => simp [init, Cfg.toTM0, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk', h]

/-- Dropping trailing blanks, as a right fold. -/
private theorem rdropWhile_eq_foldr (l : List ℕ) :
    l.rdropWhile (· == 0) = l.foldr (fun a r ↦ if a = 0 ∧ r = [] then [] else a :: r) [] := by
  have hne : ∀ (l r : List ℕ), r ≠ [] →
      l.foldr (fun a r ↦ if a = 0 ∧ r = [] then [] else a :: r) r = l ++ r := by
    intro l r hr
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih, hr]
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.rdropWhile_concat, List.foldr_append]
    by_cases ha : a = 0
    · simp [ha, ih]
    · simp only [beq_iff_eq, ha, ↓reduceIte, List.foldr_cons, List.foldr_nil]
      exact (hne l [a] (List.cons_ne_nil _ _)).symm

/-- Dropping trailing blanks does not change a half-tape. -/
private theorem mk_rdropWhile (l : List ℕ) :
    ListBlank.mk (l.rdropWhile (· == 0)) = ListBlank.mk l := by
  rw [rdropWhile_eq_foldr]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · obtain ⟨rfl, hr⟩ := h
      rw [← ListBlank.cons_mk, ← ih, hr]
      exact (ListBlank.cons_head_tail (ListBlank.mk [])).symm
    · rw [← ListBlank.cons_mk, ← ListBlank.cons_mk, ih]

/-- The output of a configuration reads as Mathlib's output. -/
theorem right₀_toTM0 (k : Cfg) : k.toTM0.Tape.right₀ = ListBlank.mk k.output := by
  rw [Cfg.output, mk_rdropWhile]
  rfl

/-- A step function that commutes with `e` on configurations satisfying an invariant `P` has
iterates that commute with `e`. -/
private theorem iterate_map {α β : Type*} {f : α → Option α} {g : β → Option β} (e : α → β)
    (P : α → Prop) (hP : ∀ a a', f a = some a' → P a → P a')
    (h : ∀ a, P a → g (e a) = (f a).map e) :
    ∀ (n : ℕ) (a : α), P a →
      (flip bind g)^[n] (some (e a)) = ((flip bind f)^[n] (some a)).map e := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a ha
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    change (flip bind g)^[n] (g (e a)) = ((flip bind f)^[n] (f a)).map e
    rw [h a ha]
    cases hfa : f a with
    | none =>
      change (flip bind g)^[n] none = ((flip bind f)^[n] none).map e
      rw [MetaMathlibExt.TM2Recursive.iterate_none_eq, MetaMathlibExt.TM2Recursive.iterate_none_eq]
      rfl
    | some a' => exact ih a' (hP a a' hfa ha)

/-- Iterates of a step function preserve an invariant that its steps preserve. -/
private theorem iterate_inv {α : Type*} {f : α → Option α} (P : α → Prop)
    (hP : ∀ a a', f a = some a' → P a → P a') :
    ∀ (n : ℕ) (a d : α), P a → (flip bind f)^[n] (some a) = some d → P d := by
  intro n
  induction n with
  | zero => intro a d ha h; cases h; exact ha
  | succ n ih =>
    intro a d ha h
    rw [Function.iterate_succ_apply] at h
    change (flip bind f)^[n] (f a) = some d at h
    cases hfa : f a with
    | none => rw [hfa, MetaMathlibExt.TM2Recursive.iterate_none_eq] at h; cases h
    | some a' => rw [hfa] at h; exact ih a' d (hP a a' hfa ha) h

/-- The iterates of the decoded machine are those of the explicit simulation. -/
theorem iterate_step_toTM0 (c : Code) (n : ℕ) (k : Cfg) :
    (flip bind (TM0.step c.machine))^[n] (some k.toTM0) =
      ((flip bind c.step)^[n] (some k)).map Cfg.toTM0 :=
  iterate_map Cfg.toTM0 (fun _ ↦ True) (fun _ _ _ _ ↦ trivial)
    (fun k _ ↦ step_toTM0 c k) n k trivial

/-- `c.machine` halts on `x` within `T` steps iff the explicit simulation does. -/
theorem haltsWithin_machine_iff (c : Code) (x : List Bool) (T : ℕ) :
    HaltsWithin c.machine (input x) T ↔
      ∃ j ≤ T, ∃ k, (flip bind c.step)^[j] (some (init x)) = some k ∧ c.step k = none := by
  simp only [HaltsWithin, ← init_toTM0, iterate_step_toTM0]
  constructor
  · rintro ⟨j, hj, d, hd, hs⟩
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hd
    rw [step_toTM0, Option.map_eq_none_iff] at hs
    exact ⟨j, hj, k, hk, hs⟩
  · rintro ⟨j, hj, k, hk, hs⟩
    exact ⟨j, hj, k.toTM0, by rw [hk]; rfl, by rw [step_toTM0, hs]; rfl⟩

/-- The configuration after `n` clocked steps is reached in some `j ≤ n` steps, and it is halted
unless `j = n`. -/
private theorem cfgAfter_spec (c : Code) (x : List Bool) (n : ℕ) :
    ∃ j ≤ n, (flip bind c.step)^[j] (some (init x)) = some (c.cfgAfter x n) ∧
      (j = n ∨ c.step (c.cfgAfter x n) = none) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  | succ n ih =>
    obtain ⟨j, hj, hjk, hor⟩ := ih
    have hsucc : c.cfgAfter x (n + 1) = c.stepOrStay (c.cfgAfter x n) := by
      simp only [cfgAfter, Function.iterate_succ_apply']
    cases hs : c.step (c.cfgAfter x n) with
    | none =>
      have hk : c.cfgAfter x (n + 1) = c.cfgAfter x n := by
        rw [hsucc, stepOrStay, hs, Option.getD_none]
      rw [hk]
      exact ⟨j, by omega, hjk, Or.inr hs⟩
    | some k' =>
      have hk : c.cfgAfter x (n + 1) = k' := by rw [hsucc, stepOrStay, hs, Option.getD_some]
      obtain rfl : j = n := hor.resolve_right (by rw [hs]; exact Option.some_ne_none _)
      refine ⟨j + 1, le_rfl, ?_, Or.inl rfl⟩
      rw [Function.iterate_succ_apply', hjk, hk]
      exact hs

/-- `evalSteps` is defined iff the clocked configuration has halted. -/
theorem isSome_evalSteps_iff_step_eq_none (c : Code) (x : List Bool) (T : ℕ) :
    (c.evalSteps x T).isSome ↔ c.step (c.cfgAfter x T) = none := by
  unfold evalSteps
  cases c.step (c.cfgAfter x T) <;> simp

/-- **Clocked halting.** `evalSteps c x T` is defined iff `c.machine` halts on the input of `x`
within `T` steps. -/
theorem isSome_evalSteps_iff (c : Code) (x : List Bool) (T : ℕ) :
    (c.evalSteps x T).isSome ↔ HaltsWithin c.machine (input x) T := by
  rw [isSome_evalSteps_iff_step_eq_none, haltsWithin_machine_iff]
  obtain ⟨j, hj, hjk, hor⟩ := cfgAfter_spec c x T
  constructor
  · intro hs
    exact ⟨j, hj, _, hjk, hs⟩
  · rintro ⟨i, hi, k, hik, hs⟩
    rcases hor with rfl | hor
    · rcases hi.lt_or_eq with hi | rfl
      · rw [MetaMathlibExt.TM2Recursive.iterate_eq_none_of_lt hik hs hi] at hjk
        cases hjk
      · rw [hik] at hjk
        cases hjk
        exact hs
    · exact hor

/-- The value of `evalSteps`, when defined, is the output of the clocked configuration. -/
theorem evalSteps_eq_some_iff_output (c : Code) (x : List Bool) (T : ℕ) (l : List ℕ) :
    c.evalSteps x T = some l ↔ c.step (c.cfgAfter x T) = none ∧ (c.cfgAfter x T).output = l := by
  unfold evalSteps
  cases c.step (c.cfgAfter x T) <;> simp

/-- **Monotonicity.** A result within `T` steps is the result for every larger clock. -/
theorem evalSteps_mono {c : Code} {x : List Bool} {T T' : ℕ} {l : List ℕ}
    (h : c.evalSteps x T = some l) (hT : T ≤ T') : c.evalSteps x T' = some l := by
  rw [evalSteps_eq_some_iff_output] at h ⊢
  obtain ⟨hs, hl⟩ := h
  have hfix : c.stepOrStay (c.cfgAfter x T) = c.cfgAfter x T := by
    rw [stepOrStay, hs, Option.getD_none]
  have hk : c.cfgAfter x T' = c.cfgAfter x T := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [cfgAfter, add_comm, Function.iterate_add_apply]
    exact Function.iterate_fixed hfix d
  rw [hk]
  exact ⟨hs, hl⟩

/-- **Agreement with `TM0.eval`.** A result of `evalSteps` is the value of the decoded machine
on the input. -/
theorem eval_eq_some_of_evalSteps_eq_some {c : Code} {x : List Bool} {T : ℕ} {l : List ℕ}
    (h : c.evalSteps x T = some l) :
    TM0.eval c.machine (input x) = Part.some (ListBlank.mk l) := by
  rw [evalSteps_eq_some_iff_output] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨j, -, hjk, -⟩ := cfgAfter_spec c x T
  have hit : (flip bind (TM0.step c.machine))^[j] (some (TM0.init (input x))) =
      some (c.cfgAfter x T).toTM0 := by
    rw [← init_toTM0, iterate_step_toTM0, hjk]
    rfl
  have hmem : (c.cfgAfter x T).toTM0 ∈ StateTransition.eval (TM0.step c.machine)
      (TM0.init (input x)) :=
    mem_eval.2 ⟨MetaMathlibExt.TM2Recursive.reaches_of_iterate_eq_some hit,
      by rw [step_toTM0, hs]; rfl⟩
  rw [TM0.eval, Part.eq_some_iff, ← right₀_toTM0]
  exact Part.mem_map _ hmem

/-- **Unclocked halting.** The decoded machine halts on the input of `x` iff some clock
suffices. -/
theorem dom_eval_iff_exists_isSome_evalSteps (c : Code) (x : List Bool) :
    (TM0.eval c.machine (input x)).Dom ↔ ∃ T, (c.evalSteps x T).isSome := by
  simp only [dom_eval_iff_exists_haltsWithin, isSome_evalSteps_iff]

/-! ### Every finite machine has a code -/

section Universality

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The action code of a statement whose written symbols are relabelled by `f`. -/
private def encStmt (f : Γ → ℕ) : TM0.Stmt Γ → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write a => f a + 2

/-- Decoding an encoded statement relabels its written symbol. -/
private theorem decodeStmt_encStmt (f : PointedMap Γ ℕ) (s : TM0.Stmt Γ) :
    decodeStmt (encStmt f s) = s.map f := by
  rcases s with (_ | _) | a <;> rfl

/-- `(T.map f).right₀ = T.right₀.map f`. -/
private theorem right₀_map {Γ' : Type*} [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) :
    (T.map f).right₀ = T.right₀.map f := by
  simp [Tape.right₀, Tape.map, ListBlank.map_cons]

/-- **Universality of codes**, for machines that read bit inputs. Every `TM0` machine with a
finite alphabet, a finite set of states supporting it (`TM0.Supports`), and two distinct non-blank
input symbols `ι false`, `ι true` has a code. (So the alphabet has at least three symbols; a
machine over a smaller alphabet cannot read a bit input.) The code simulates it step for step after
an injective relabelling `f` of the symbols, which sends the input symbols `ι b` to `bitSym b`: it
has the same results up to `f` and halts within the same number of steps. -/
theorem exists_code [Finite Γ] (M : TM0.Machine Γ Λ) {S : Set Λ} (hS : TM0.Supports M S)
    (hSf : S.Finite) (ι : Bool → Γ) (hι : Function.Injective ι) (hι0 : ∀ b, ι b ≠ default) :
    ∃ (c : Code) (f : PointedMap Γ ℕ), Function.Injective f ∧ (∀ b, f (ι b) = bitSym b) ∧
      (∀ l, TM0.eval c.machine (l.map f) = (TM0.eval M l).map (ListBlank.map f)) ∧
      ∀ l T, HaltsWithin c.machine (l.map f) T ↔ HaltsWithin M l T := by
  classical
  have := Fintype.ofFinite Γ
  -- number the states of `S` and the symbols, with the initial state and the blank first
  let L : List Λ := default :: hSf.toFinset.toList
  let Lg : List Γ := default :: ι false :: ι true :: Finset.univ.toList
  let g : PointedMap Λ ℕ := ⟨fun q ↦ L.idxOf q, List.idxOf_cons_self⟩
  let f : PointedMap Γ ℕ := ⟨fun a ↦ Lg.idxOf a, List.idxOf_cons_self⟩
  have hL : ∀ q ∈ S, L[g q]? = some q := fun q hq ↦
    List.getElem?_idxOf (List.mem_cons_of_mem _ (by simpa using hq))
  have hLg : ∀ a, Lg[f a]? = some a := fun a ↦
    List.getElem?_idxOf (by simp [Lg])
  let c : Code := ⟨L.map fun q ↦ Lg.map fun a ↦ (M q a).map fun p ↦ (g p.1, encStmt f p.2)⟩
  have hc : ∀ q ∈ S, ∀ a, c.machine (g q) (f a) = (M q a).map (Prod.map g (TM0.Stmt.map f)) := by
    intro q hq a
    simp only [machine, lookup, c, List.getElem?_map, hL q hq, hLg a, Option.map_some,
      Option.bind_some, Option.join_some, Option.map_map]
    congr 1
    funext p
    simp only [Function.comp_apply, decodeStmt_encStmt]
    rfl
  have hfinj : Function.Injective f := fun a b h ↦ by
    have := hLg a
    rw [show f a = f b from h, hLg b] at this
    exact (Option.some.inj this).symm
  have hf : ∀ b, f (ι b) = bitSym b := by
    have h1 : ι false ≠ default := hι0 false
    have h2 : ι true ≠ default := hι0 true
    have h3 : ι true ≠ ι false := fun h ↦ Bool.noConfusion (hι h)
    intro b
    cases b
    · change Lg.idxOf (ι false) = 1
      simp only [Lg, List.idxOf_cons_ne _ h1.symm, List.idxOf_cons_self]
    · change Lg.idxOf (ι true) = 2
      simp only [Lg, List.idxOf_cons_ne _ h2.symm, List.idxOf_cons_ne _ h3.symm,
        List.idxOf_cons_self]
  -- the decoded machine follows `M` on supported configurations
  have hstep : ∀ d : TM0.Cfg Γ Λ, d.q ∈ S →
      TM0.step c.machine (d.map f g) = (TM0.step M d).map (TM0.Cfg.map f g) := by
    rintro ⟨q, T⟩ hq
    simp only [TM0.Cfg.map, TM0.step, Tape.map_fst, hc q hq, Option.map_map]
    congr 1
    funext p
    obtain ⟨q', (d | a)⟩ := p
    · simp [TM0.Stmt.map, TM0.Cfg.map, Tape.map_move]
    · simp [TM0.Stmt.map, TM0.Cfg.map, Tape.map_write]
  have hinv : ∀ a a', TM0.step M a = some a' → a.q ∈ S → a'.q ∈ S :=
    fun a a' h ha ↦ TM0.step_supports M hS h ha
  have hit : ∀ n (d : TM0.Cfg Γ Λ), d.q ∈ S →
      (flip bind (TM0.step c.machine))^[n] (some (d.map f g)) =
        ((flip bind (TM0.step M))^[n] (some d)).map (TM0.Cfg.map f g) :=
    iterate_map (TM0.Cfg.map f g) (fun d ↦ d.q ∈ S) hinv hstep
  have hinit : ∀ l : List Γ, (TM0.init l).map f g = TM0.init (l.map f) := TM0.map_init f g
  have hR : Respects (TM0.step M) (TM0.step c.machine)
      fun a b ↦ a.q ∈ S ∧ TM0.Cfg.map f g a = b := by
    rintro a _ ⟨ha, rfl⟩
    cases e : TM0.step M a with
    | none => simp only; rw [hstep a ha, e]; rfl
    | some a' =>
      refine ⟨_, ⟨hinv a a' e ha, rfl⟩, Relation.TransGen.single ?_⟩
      rw [hstep a ha, e]
      rfl
  refine ⟨c, f, hfinj, hf, fun l ↦ ?_, fun l T ↦ ?_⟩
  · have hi : (TM0.init l : TM0.Cfg Γ Λ).q ∈ S := hS.1
    apply Part.ext
    intro b
    rw [TM0.eval, TM0.eval, ← hinit, Part.map_map, Part.mem_map_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨d₁, ⟨-, rfl⟩, hd₁⟩ := tr_eval_rev hR ⟨hi, rfl⟩ hd
      exact ⟨d₁, hd₁, (right₀_map f d₁.Tape).symm⟩
    · rintro ⟨d₁, hd₁, rfl⟩
      obtain ⟨d, ⟨-, rfl⟩, hd⟩ := tr_eval hR ⟨hi, rfl⟩ hd₁
      exact ⟨_, hd, right₀_map f d₁.Tape⟩
  · have hi : (TM0.init l : TM0.Cfg Γ Λ).q ∈ S := hS.1
    simp only [HaltsWithin, ← hinit, hit _ _ hi]
    constructor
    · rintro ⟨j, hj, d', hd', hs⟩
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hd'
      have hdS := iterate_inv (fun d : TM0.Cfg Γ Λ ↦ d.q ∈ S) hinv j _ d hi hd
      rw [hstep d hdS, Option.map_eq_none_iff] at hs
      exact ⟨j, hj, d, hd, hs⟩
    · rintro ⟨j, hj, d, hd, hs⟩
      have hdS := iterate_inv (fun d : TM0.Cfg Γ Λ ↦ d.q ∈ S) hinv j _ d hi hd
      exact ⟨j, hj, d.map f g, by rw [hd]; rfl, by rw [hstep d hdS, hs]; rfl⟩

end Universality

/-! ### Primitive recursiveness -/

section Primrec

/-- The table of a code is primitive recursive. -/
private theorem primrec_table : Primrec Code.table :=
  Primrec.of_equiv (e := equivTable)

/-- The state of a configuration is primitive recursive. -/
private theorem primrec_cfg_q : Primrec Cfg.q :=
  Primrec.fst.comp (Primrec.of_equiv (e := Cfg.equivProd))

/-- The left cells of a configuration are primitive recursive. -/
private theorem primrec_cfg_left : Primrec Cfg.left :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Cfg.equivProd)))

/-- The head cell of a configuration is primitive recursive. -/
private theorem primrec_cfg_head : Primrec Cfg.head :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Cfg.equivProd))))

/-- The right cells of a configuration are primitive recursive. -/
private theorem primrec_cfg_right : Primrec Cfg.right :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Cfg.equivProd))))

/-- Building a configuration from primitive recursive parts is primitive recursive. -/
private theorem primrec_cfg_mk {α : Type*} [Primcodable α] {f₁ : α → ℕ} {f₂ : α → List ℕ}
    {f₃ : α → ℕ} {f₄ : α → List ℕ} (h₁ : Primrec f₁) (h₂ : Primrec f₂) (h₃ : Primrec f₃)
    (h₄ : Primrec f₄) : Primrec fun a ↦ Cfg.mk (f₁ a) (f₂ a) (f₃ a) (f₄ a) :=
  (Primrec.of_equiv_symm (e := Cfg.equivProd)).comp (h₁.pair (h₂.pair (h₃.pair h₄)))

/-- Table lookup is primitive recursive. -/
private theorem primrec_lookup : Primrec fun p : Code × ℕ × ℕ ↦ p.1.lookup p.2.1 p.2.2 := by
  have h : Primrec fun p : Code × ℕ × ℕ ↦ p.1.table[p.2.1]?.bind fun row ↦ row[p.2.2]? :=
    Primrec.option_bind (Primrec.list_getElem?.comp (primrec_table.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
      (Primrec.list_getElem?.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.option_bind h Primrec₂.right).of_eq fun p ↦ by
    simp only [lookup]
    cases p.1.table[p.2.1]?.bind fun row ↦ row[p.2.2]? <;> rfl

/-- Doing an action is primitive recursive. -/
private theorem primrec_act : Primrec fun p : Cfg × ℕ × ℕ ↦ p.1.act p.2.1 p.2.2 := by
  have hk : Primrec fun p : Cfg × ℕ × ℕ ↦ p.1 := Primrec.fst
  have hq : Primrec fun p : Cfg × ℕ × ℕ ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  have h0 : Primrec fun p : Cfg × ℕ × ℕ ↦
      (⟨p.2.1, p.1.left.tail, p.1.left.headI, p.1.head :: p.1.right⟩ : Cfg) :=
    primrec_cfg_mk hq (Primrec.list_tail.comp (primrec_cfg_left.comp hk))
      (Primrec.list_headI.comp (primrec_cfg_left.comp hk))
      (Primrec.list_cons.comp (primrec_cfg_head.comp hk) (primrec_cfg_right.comp hk))
  have h1 : Primrec fun p : Cfg × ℕ × ℕ ↦
      (⟨p.2.1, p.1.head :: p.1.left, p.1.right.headI, p.1.right.tail⟩ : Cfg) :=
    primrec_cfg_mk hq (Primrec.list_cons.comp (primrec_cfg_head.comp hk) (primrec_cfg_left.comp hk))
      (Primrec.list_headI.comp (primrec_cfg_right.comp hk))
      (Primrec.list_tail.comp (primrec_cfg_right.comp hk))
  have h2 : Primrec₂ fun (p : Cfg × ℕ × ℕ) (a : ℕ) ↦ (⟨p.2.1, p.1.left, a, p.1.right⟩ : Cfg) :=
    primrec_cfg_mk (hq.comp Primrec.fst) (primrec_cfg_left.comp (hk.comp Primrec.fst))
      Primrec.snd (primrec_cfg_right.comp (hk.comp Primrec.fst))
  have h12 : Primrec₂ fun (p : Cfg × ℕ × ℕ) (n : ℕ) ↦ Nat.casesOn (motive := fun _ ↦ Cfg) n
      (⟨p.2.1, p.1.head :: p.1.left, p.1.right.headI, p.1.right.tail⟩ : Cfg)
      fun a ↦ (⟨p.2.1, p.1.left, a, p.1.right⟩ : Cfg) :=
    Primrec.nat_casesOn Primrec.snd (h1.comp Primrec.fst)
      (h2.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  refine (Primrec.nat_casesOn (Primrec.snd.comp Primrec.snd) h0 h12).of_eq fun p ↦ ?_
  obtain ⟨k, q', _ | _ | a⟩ := p <;> rfl

/-- One simulated step is primitive recursive. -/
private theorem primrec_step : Primrec fun p : Code × Cfg ↦ p.1.step p.2 :=
  Primrec.option_map (primrec_lookup.comp (Primrec.fst.pair
      ((primrec_cfg_q.comp Primrec.snd).pair (primrec_cfg_head.comp Primrec.snd))))
    (primrec_act.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

/-- The initial configuration is primitive recursive in the input. -/
private theorem primrec_init : Primrec init := by
  have hin : Primrec input :=
    Primrec.list_map Primrec.id ((Primrec.dom_finite bitSym).comp Primrec.snd).to₂
  exact primrec_cfg_mk (Primrec.const 0) (Primrec.const []) (Primrec.list_headI.comp hin)
    (Primrec.list_tail.comp hin)

/-- The output of a configuration is primitive recursive. -/
private theorem primrec_output : Primrec Cfg.output := by
  have hl : Primrec fun k : Cfg ↦ k.head :: k.right :=
    Primrec.list_cons.comp primrec_cfg_head primrec_cfg_right
  have hf : Primrec₂ fun (_ : Cfg) (p : ℕ × List ℕ) ↦
      if p.1 = 0 ∧ p.2 = [] then [] else p.1 :: p.2 := by
    refine Primrec.ite (PrimrecPred.and ?_ ?_) (Primrec.const []) ?_
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
    · exact Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
    · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hl (Primrec.const []) hf).of_eq fun k ↦ by
    rw [Cfg.output, rdropWhile_eq_foldr]

/-- **Computability.** The clocked evaluator is primitive recursive in the code, the input and
the clock. -/
theorem primrec_evalSteps :
    Primrec fun p : Code × List Bool × ℕ ↦ p.1.evalSteps p.2.1 p.2.2 := by
  have hstay : Primrec₂ fun (p : Code × List Bool × ℕ) (k : Cfg) ↦ p.1.stepOrStay k :=
    Primrec.option_getD.comp (primrec_step.comp ((Primrec.fst.comp Primrec.fst).pair
      Primrec.snd)) Primrec.snd
  have hk : Primrec fun p : Code × List Bool × ℕ ↦ p.1.cfgAfter p.2.1 p.2.2 :=
    Primrec.nat_iterate (Primrec.snd.comp Primrec.snd)
      (primrec_init.comp (Primrec.fst.comp Primrec.snd)) hstay
  refine (Primrec.option_casesOn (primrec_step.comp (Primrec.fst.pair hk))
    (Primrec.option_some.comp (primrec_output.comp hk)) (Primrec.const none).to₂).of_eq
    fun p ↦ ?_
  simp only [evalSteps]
  cases p.1.step (p.1.cfgAfter p.2.1 p.2.2) <;> rfl

end Primrec

end Code

end Cslib.Turing.Universal
