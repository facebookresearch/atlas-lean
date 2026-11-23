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

/-- **Bounded halting of a single-tape machine.** A single-tape Turing machine $M$ halts within
$T$ steps on a word $l$ when, started in its initial state with $l$ on the tape and the head on
the first letter of $l$ (on a blank if $l$ is empty), it reaches after some $j \le T$ steps a
configuration that has no successor. -/
def HaltsWithin (M : TM0.Machine Γ Λ) (l : List Γ) (T : ℕ) : Prop :=
  ∃ j ≤ T, ∃ d, (flip bind (TM0.step M))^[j] (some (TM0.init l)) = some d ∧ TM0.step M d = none

/-- **Halting within a bound is monotone in the bound.** For a single-tape Turing machine $M$,
a list $l$ of symbols and numbers $T \le T'$, if $M$ started on $l$ halts within $T$ steps,
then $M$ started on $l$ halts within $T'$ steps. -/
theorem HaltsWithin.mono {M : TM0.Machine Γ Λ} {l : List Γ} {T T' : ℕ} (h : HaltsWithin M l T)
    (hT : T ≤ T') : HaltsWithin M l T' := by
  obtain ⟨j, hj, d, hd⟩ := h
  exact ⟨j, hj.trans hT, d, hd⟩

/-- **Halting is halting within some number of steps.** For a single-tape Turing machine $M$ and
an input word $l$, the evaluation of $M$ on $l$ is defined (that is, $M$ halts on $l$) if and only
if there is $T \in \mathbb{N}$ such that $M$ halts on $l$ within $T$ steps. -/
theorem dom_eval_iff_exists_haltsWithin (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ ∃ T, HaltsWithin M l T := by
  rw [TM0.eval, Part.map_Dom, MetaMathlibExt.TM2Recursive.dom_eval_iff_exists_iterate]
  exact ⟨fun ⟨j, d, hd⟩ ↦ ⟨j, j, le_rfl, d, hd⟩, fun ⟨_, j, _, d, hd⟩ ↦ ⟨j, d, hd⟩⟩

end HaltsWithin

/-! ### Codes -/

/-- **Codes for single-tape machines.** A code is a transition table: a finite list of rows, row
$q$ belonging to the state $q \in \mathbb{N}$, each a finite list of entries, entry $a$ of a row
belonging to the symbol $a \in \mathbb{N}$. The entry in row $q$ and column $a$ is either empty,
meaning that the machine halts, or a pair $(q', s)$ of natural numbers, meaning that the machine
enters the state $q'$ and does the action coded by $s$: $0$ moves left, $1$ moves right and
$b + 2$ writes $b$. A state or symbol outside the table halts the machine. -/
structure Code where
  /-- The transition table, indexed by state, then by symbol. -/
  table : List (List (Option (ℕ × ℕ)))
  deriving DecidableEq

/-- **Decoding an action.** A natural number codes a statement of a single-tape Turing machine
with symbols in $\mathbb{N}$: $0$ moves the head left, $1$ moves the head right, and $a + 2$ writes
the symbol $a$. -/
def decodeStmt : ℕ → TM0.Stmt ℕ
  | 0 => .move .left
  | 1 => .move .right
  | a + 2 => .write a

/-- **Symbol of an input bit.** The tape symbol of a bit $b$ is $1$ if $b$ is false and $2$ if $b$
is true; the symbol $0$ is the blank. -/
def bitSym (b : Bool) : ℕ := cond b 2 1

/-- **Input word of a list of bits.** The input word of a list of bits $x$ is the list of natural
numbers obtained from $x$ by replacing each bit by its symbol: $1$ for false and $2$ for true. -/
def input (x : List Bool) : List ℕ := x.map bitSym

namespace Code

/-- **Single-tape codes as tables.** Codes for single-tape machines correspond bijectively to
transition tables, that is, to lists of rows, each a list of entries that are either empty or a
pair of natural numbers: a code corresponds to its table. -/
def equivTable : Code ≃ List (List (Option (ℕ × ℕ))) where
  toFun := table
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Codes are coded as their tables. -/
instance : Primcodable Code := Primcodable.ofEquiv _ equivTable

/-- **Table lookup of a code.** For a code $c$ and numbers $q$ and $a$, the lookup of $c$ at
state $q$ and symbol $a$ is the entry in row $q$, column $a$ of the table of $c$: either a pair
$(q', s)$ of a next state and an action code, or no entry (halt). It is no entry when the
table has no row $q$ or that row has no column $a$. -/
def lookup (c : Code) (q a : ℕ) : Option (ℕ × ℕ) := (c.table[q]?.bind fun row ↦ row[a]?).join

/-- **The machine of a single-tape code.** The machine of a code $c$ is the single-tape Turing
machine with states and symbols in $\mathbb{N}$ that, in state $q$ reading symbol $a$, halts if
the table lookup of $c$ at state $q$ and symbol $a$ has no entry, and otherwise, if the entry is
$(q', s)$, enters state $q'$ and does the action coded by $s$: $0$ moves left, $1$ moves right
and $a' + 2$ writes $a'$. -/
def machine (c : Code) : TM0.Machine ℕ ℕ := fun q a ↦
  (c.lookup q a).map fun e ↦ (e.1, decodeStmt e.2)

/-- **States of a single-tape code.** The set of states of a code $c$ is the finite set of natural
numbers consisting of the initial state $0$ and every state $q'$ such that some entry of the
table of $c$ is a pair $(q', s)$. -/
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

/-- **Explicit configurations.** A configuration of the simulation consists of a state
$q \in \mathbb{N}$, the list of the cells left of the head (nearest first), the symbol in the cell
under the head, and the list of the cells right of the head (nearest first); states and symbols
are natural numbers. -/
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

/-- **Configurations as tuples.** Configurations correspond bijectively to tuples in
$\mathbb{N} \times \mathrm{List}(\mathbb{N}) \times \mathbb{N} \times \mathrm{List}(\mathbb{N})$:
a configuration corresponds to the tuple of its state, its cells left of the head, its cell under
the head and its cells right of the head. -/
def Cfg.equivProd : Cfg ≃ ℕ × List ℕ × ℕ × List ℕ where
  toFun k := (k.q, k.left, k.head, k.right)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Configurations are coded as tuples. -/
instance : Primcodable Cfg := Primcodable.ofEquiv _ Cfg.equivProd

/-- **TM0 configuration of a simulation configuration.** The TM0 configuration of a configuration
$k$ of the simulation has the state of $k$, the cell under the head of $k$ as its head cell, and
as the halves of its tape left and right of the head the cells of $k$ left and right of the head,
nearest first, followed by infinitely many blanks. -/
def Cfg.toTM0 (k : Cfg) : TM0.Cfg ℕ ℕ := ⟨k.q, ⟨k.head, ListBlank.mk k.left, ListBlank.mk k.right⟩⟩

/-- **Acting on a configuration.** Let $k$ be a configuration with left cells $L$ (nearest
first), head cell $h$ and right cells $R$ (nearest first), let $q'$ be a state and let $s$ be an
action code. Acting on $k$ with $q'$ and $s$ gives a configuration with state $q'$, as follows.
For $s = 0$ (move left), its head cell is the first entry of $L$, or the blank $0$ if $L$ is
empty, its left cells are $L$ without its first entry, and its right cells are $h$ followed by
$R$. For $s = 1$ (move right), its head cell is the first entry of $R$, or $0$ if $R$ is empty,
its right cells are $R$ without its first entry, and its left cells are $h$ followed by $L$. For
$s = a + 2$ (write $a$), its head cell is $a$ and its left and right cells are $L$ and $R$. -/
def Cfg.act (k : Cfg) (q' : ℕ) : ℕ → Cfg
  | 0 => ⟨q', k.left.tail, k.left.headI, k.head :: k.right⟩
  | 1 => ⟨q', k.head :: k.left, k.right.headI, k.right.tail⟩
  | a + 2 => ⟨q', k.left, a, k.right⟩

/-- **Output of a configuration.** The output of a configuration $k$ is the list consisting of the
symbol under the head of $k$ followed by the cells right of the head (nearest first), with all
trailing blanks $0$ removed. -/
def Cfg.output (k : Cfg) : List ℕ := (k.head :: k.right).rdropWhile (· == 0)

/-- **Initial configuration of the code simulation.** The initial configuration of the
simulation on a list of bits $x$ has state $0$, an empty list of cells left of the head, the
head on the first symbol of the input word of $x$ (the blank $0$ if $x$ is empty), and the
remaining symbols of the input word, in order, right of the head. -/
def init (x : List Bool) : Cfg := ⟨0, [], (input x).headI, (input x).tail⟩

/-- **One step of a code.** For a code $c$ and a configuration $k$ of the simulation, look up the
table entry of $c$ at the state of $k$ and the symbol under the head of $k$. If there is no entry,
the step is undefined (the machine halts); if the entry is $(q', s)$, the step is the
configuration obtained from $k$ by entering the state $q'$ and doing the action coded by $s$. -/
def step (c : Code) (k : Cfg) : Option Cfg := (c.lookup k.q k.head).map fun e ↦ k.act e.1 e.2

/-- **One step of a code, or stay when halted.** For a code $c$ and a configuration $k$ of the
simulation, the configuration after one step of $c$ from $k$ if that step is defined, and $k$
itself if $c$ halts at $k$. -/
def stepOrStay (c : Code) (k : Cfg) : Cfg := (c.step k).getD k

/-- **Clocked configuration of a code.** For a code $c$, a list of bits $x$ and $T \in \mathbb{N}$,
the configuration of $c$ on $x$ after $T$ steps is obtained from the initial configuration on $x$
by applying $T$ times the step of $c$, where a step leaves a halted configuration unchanged. It is
the configuration after $T$ steps, or the halting configuration if the machine halts earlier. -/
def cfgAfter (c : Code) (x : List Bool) (T : ℕ) : Cfg := c.stepOrStay^[T] (init x)

/-- **The clocked evaluator.** Given a code $c$, a list of bits $x$ and a clock $T \in \mathbb{N}$,
run the simulation of $c$ on $x$ for at most $T$ steps. If it halts within $T$ steps, the result
is the output of the halting configuration: the tape from the head rightwards, with trailing
blanks dropped. Otherwise there is no result. -/
def evalSteps (c : Code) (x : List Bool) (T : ℕ) : Option (List ℕ) :=
  (c.step (c.cfgAfter x T)).elim (some (c.cfgAfter x T).output) fun _ ↦ none

/-! ### Agreement with Mathlib's semantics -/

/-- **Explicit steps agree with the decoded machine.** For every code $c$ and every configuration
$k$ of the simulation, the decoded TM0 machine of $c$ halts at the TM0 configuration of $k$
exactly when the step of $c$ from $k$ is undefined, and otherwise its step from the TM0
configuration of $k$ is the TM0 configuration of the step of $c$ from $k$. -/
theorem step_toTM0 (c : Code) (k : Cfg) :
    TM0.step c.machine k.toTM0 = (c.step k).map Cfg.toTM0 := by
  simp only [TM0.step, Cfg.toTM0, machine, step, Option.map_map]
  congr 1
  funext e
  obtain ⟨q', _ | _ | a⟩ := e <;>
    simp [decodeStmt, Cfg.act, Cfg.toTM0, Tape.move, Tape.write, ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]

/-- **The explicit initial configuration is the machine's.** For a list of bits $x$, the initial
configuration of the simulation on $x$, read as a configuration of a single-tape machine, is the
initial configuration of a single-tape machine on the input word of $x$. -/
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

/-- **The output of a configuration as a Mathlib half-tape.** For every explicit configuration
$k$, the half-tape of the Mathlib configuration of $k$ from the head rightwards (the cell under
the head followed by the cells to its right) is the output of $k$, read with blanks beyond its
end. -/
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

/-- **Iterated steps of the decoded machine.** Let $c$ be a code, $n \in \mathbb{N}$ and $k$
an explicit configuration. Run the machine of $c$ for $n$ steps from the Mathlib configuration
of $k$, and run the explicit simulation of $c$ for $n$ steps from $k$, where a run that reaches
a configuration without a successor before completing $n$ steps has no result. Then the first
run has a result exactly when the second does, and its result is the Mathlib configuration of
the result of the second. -/
theorem iterate_step_toTM0 (c : Code) (n : ℕ) (k : Cfg) :
    (flip bind (TM0.step c.machine))^[n] (some k.toTM0) =
      ((flip bind c.step)^[n] (some k)).map Cfg.toTM0 :=
  iterate_map Cfg.toTM0 (fun _ ↦ True) (fun _ _ _ _ ↦ trivial)
    (fun k _ ↦ step_toTM0 c k) n k trivial

/-- **Bounded halting of a decoded machine through its simulation.** For a code $c$, a list of
bits $x$ and $T \in \mathbb{N}$, the decoded machine of $c$ halts within $T$ steps on the input
word of $x$ if and only if the explicit simulation of $c$, started from the initial configuration
on $x$, reaches after some $j \le T$ steps a configuration that has no successor step. -/
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

/-- **Definedness of the clocked evaluator.** For a code $c$, a list of bits $x$ and a clock
$T \in \mathbb{N}$, the clocked evaluator of $c$ on $x$ with clock $T$ returns a value if and
only if the simulation of $c$ has no step from the configuration after $T$ clocked steps on $x$
(the configuration after $T$ steps, or the halting configuration if the machine halts
earlier). -/
theorem isSome_evalSteps_iff_step_eq_none (c : Code) (x : List Bool) (T : ℕ) :
    (c.evalSteps x T).isSome ↔ c.step (c.cfgAfter x T) = none := by
  unfold evalSteps
  cases c.step (c.cfgAfter x T) <;> simp

/-- **Clocked halting.** For a code $c$, a list of bits $x$ and a clock $T \in \mathbb{N}$,
the clocked evaluator of $c$ on $x$ with clock $T$ returns a value if and only if the machine
of $c$, started on the input word of $x$, halts within $T$ steps. -/
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

/-- **Characterization of clocked results.** For a code $c$, a list of bits $x$, a clock
$T \in \mathbb{N}$ and a list $l$ of natural numbers, the clocked evaluator returns $l$ on $c$,
$x$ and $T$ if and only if the configuration of $c$ after $T$ clocked steps on $x$ has no
successor step and its output is $l$. -/
theorem evalSteps_eq_some_iff_output (c : Code) (x : List Bool) (T : ℕ) (l : List ℕ) :
    c.evalSteps x T = some l ↔ c.step (c.cfgAfter x T) = none ∧ (c.cfgAfter x T).output = l := by
  unfold evalSteps
  cases c.step (c.cfgAfter x T) <;> simp

/-- **Monotonicity of the single-tape clocked evaluator.** Let $c$ be a code for a single-tape
machine, $x$ a list of bits, $l$ a list of natural numbers and $T \le T'$ natural numbers. If the
clocked evaluator returns $l$ on $c$ and $x$ with clock $T$, then it also returns $l$ with clock
$T'$. -/
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

/-- **Clocked results agree with the machine's semantics.** Let $c$ be a code, $x$ a list of
bits, $T$ a natural number and $l$ a list of natural numbers. If the clocked evaluator, running
$c$ on $x$ for at most $T$ steps, returns $l$, then the decoded machine of $c$, started on the
input word of $x$, halts, and the tape from its head rightwards in the halting configuration is
$l$ followed by blanks. -/
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

/-- **Unclocked halting.** For a code $c$ and a list of bits $x$, the machine decoded from $c$ halts
on the input word of $x$ if and only if there is a clock $T \in \mathbb{N}$ for which the clocked
evaluator of $c$ on $x$ with clock $T$ returns a result. -/
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

/-- **Universality of codes**, for machines that read bit inputs. Let $M$ be a single-tape
Turing machine with a finite alphabet $\Gamma$ and a finite set of states that contains the
initial state and is closed under the transitions of $M$, and let $\iota$ be an injective map
from the bits to $\Gamma$ whose values are not the blank. Then there are a code $c$ and an
injective map $f$ from $\Gamma$ to the natural numbers, sending the blank to $0$ and each
$\iota(b)$ to the symbol of the bit $b$, such that for every word $l$ over $\Gamma$, writing
$f(l)$ for the word obtained by applying $f$ to each letter: the decoded machine of $c$ halts on
$f(l)$ exactly when $M$ halts on $l$, and its result (the tape from the head rightwards when it
halts) is then the result of $M$ on $l$ with $f$ applied to each cell; and for every
$T \in \mathbb{N}$, the decoded machine of $c$ halts within $T$ steps on $f(l)$ if and only if
$M$ halts within $T$ steps on $l$.

(So the alphabet has at least three symbols; a machine over a smaller alphabet cannot read a bit
input.) -/
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

/-- **The clocked evaluator is primitive recursive.** The clocked evaluator is primitive
recursive in the code, the input and the clock. -/
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
