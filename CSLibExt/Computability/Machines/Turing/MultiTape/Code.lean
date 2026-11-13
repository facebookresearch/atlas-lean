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
is in `MultiTape/CodeCompleteness.lean`; a universal *machine* is not built here.

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

/-- **Coded actions.** A coded action for a machine with $k$ work tapes consists of a coded
input-head move; for each of the $k$ work tapes, an optional symbol to write, the symbol being a
bit or the blank (so a blank can be written), together with a coded head move; an optional
output bit; and an optional next state in $\mathbb{N}$, where no next state means halting. A
head move is coded by a natural number: $0$ moves left, $1$ stays, and any other number moves
right. -/
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

/-- **Coded actions as tuples.** The bijection between coded actions and tuples $(m, w, b, q)$
that sends an action to its coded input head move $m \in \mathbb{N}$, its work tape instructions
$w$ (for each of the $k$ work tapes, an optional symbol to write and a coded head move), its
optional output bit $b$ and its optional next state $q$. -/
def equivProd :
    CodeAction k ≃ ℕ × (Fin k → Option (Option Bool) × ℕ) × Option Bool × Option ℕ where
  toFun a := (a.inputMove, a.work, a.out, a.next)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (CodeAction k) := Primcodable.ofEquiv _ equivProd

/-- **Decoding a coded action.** A coded action $a$ stands for the action of CSLib's multi-tape
model that moves the input head by the decoded input move of $a$, on each work tape writes the
optional symbol that $a$ gives for that tape and moves its head by the decoded move, emits the
optional output bit of $a$, and enters the next state of $a$ (halting when there is none). -/
def toAction (a : CodeAction k) : Action k Bool ℕ where
  inputTape := decodeMove a.inputMove
  workTapes i := ((a.work i).1, decodeMove (a.work i).2)
  output := a.out
  state := a.next

/-- **Halting action.** The default action of a missing table entry: halt without moving any
head, writing any symbol or emitting an output bit. -/
def halt : CodeAction k := ⟨1, fun _ ↦ (none, 1), none, none⟩

end CodeAction

/-- **Keys of a code's table.** A key of a table entry for a machine with $k$ work tapes is a
triple $(q, a, w)$ of a state $q \in \mathbb{N}$, the symbol $a$ under the input head and the
symbols $w = (w_i)_{i < k}$ under the $k$ work heads, where each symbol is a bit or the blank. -/
abbrev CodeKey (k : ℕ) := ℕ × Option Bool × (Fin k → Option Bool)

/-- **Codes for multi-tape machines.** A code for a machine with $k$ work tapes over the binary
alphabet, with states in $\mathbb{N}$, is a finite list of table entries, each a key (a state
together with the symbols under the input head and the $k$ work heads) paired with a coded
action. The table is looked up by key, the first matching entry wins, and a missing key halts
the machine. -/
structure Code (k : ℕ) where
  /-- The table entries. -/
  table : List (CodeKey k × CodeAction k)

namespace Code

/-- **Multi-tape codes as tables.** The bijection between codes for machines with $k$ work tapes
and finite lists of table entries, each a pair of a key and a coded action, that sends a code to
its table. -/
def equivTable : Code k ≃ List (CodeKey k × CodeAction k) where
  toFun := table
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (Code k) := Primcodable.ofEquiv _ equivTable

/-- **Numeric coding of codes.** The natural number coding a code $c$: its encoding under the
standard primitive recursive coding of codes, which identifies a code with its table, a list of
pairs of a key and a coded action. -/
def encode (c : Code k) : ℕ := Encodable.encode c

/-- **Decoding numbers to codes.** The code coded by a natural number $n$, if any: decoding
under the standard primitive recursive coding of codes, which identifies a code with its table,
a list of pairs of a key and a coded action. The result is empty when $n$ codes no code. -/
def decode (n : ℕ) : Option (Code k) := Encodable.decode n

/-- **Code round-trip.** For every code $c$ with $k$ work tapes, decoding the natural number
$\operatorname{encode}(c)$ returns $c$: $\operatorname{decode}(\operatorname{encode}(c))$ is
defined and equals $c$. -/
@[simp]
theorem decode_encode (c : Code k) : decode (encode c) = some c :=
  Encodable.encodek c

/-- **Injectivity of the numeric coding of codes.** If two codes $c$ and $c'$ with the same
number of work tapes have the same numeric code, then $c = c'$. -/
theorem encode_injective : Function.Injective (encode (k := k)) :=
  Encodable.encode_injective

/-- **Action of a code at a key.** For a code $c$ with $k$ work tapes, a state
$q \in \mathbb{N}$, a symbol $a$ under the input head and symbols $w = (w_i)_{i < k}$ under the
work heads (each symbol a bit or the blank), the action of $c$ at $(q, a, w)$ is the coded action
of the first table entry of $c$ whose key is $(q, a, w)$, or, if there is no such entry, the
halting action, which moves no head, writes and emits nothing, and has no next state. -/
def act (c : Code k) (q : ℕ) (a : Option Bool) (w : Fin k → Option Bool) : CodeAction k :=
  ((@List.lookup _ _ instBEqOfDecidableEq (q, a, w) c.table)).getD CodeAction.halt

/-- **Transition function of a code.** The transition function of a code $c$ sends a state $q$,
the symbol $a$ under the input head and the symbols $w$ under the work heads (each a bit or
blank) to the action of CSLib's multi-tape model that the coded action of $c$ at $(q, a, w)$
stands for. That coded action is the one of the first table entry of $c$ with key $(q, a, w)$,
or, if there is none, the one that halts without moving, writing or emitting. -/
def tr (c : Code k) (q : ℕ) (a : Option Bool) (w : Fin k → Option Bool) : Action k Bool ℕ :=
  (c.act q a w).toAction

/-- **The multi-tape machine of a code.** The machine of a code $c$ for $k$ work tapes is the
machine of CSLib's multi-tape model with $k$ work tapes, the binary alphabet and states in
$\mathbb{N}$ whose initial state is $0$ and whose transition function is the transition function
of $c$. -/
noncomputable def toTM (c : Code k) : MultiTapeTM k Bool ℕ := MultiTapeTM.ofTr 0 c.tr

@[simp]
theorem q₀_toTM (c : Code k) : c.toTM.q₀ = 0 := rfl

/-- **Step of the machine of a code.** For a code $c$, a binary input $x$ and a configuration $C$
of the machine of $c$ on $x$, the step of the machine of $c$ sends $C$ to its successor under
the transition function of $c$: $C$ itself if it has halted, and otherwise the result of
applying to $C$ the action that the transition function of $c$ selects for the state of $C$ and
the symbols under its heads. -/
theorem step_toTM (c : Code k) {x : List Bool} (cfg : Cfg k Bool ℕ x) :
    c.toTM.step cfg = stepWith c.tr cfg :=
  step_ofTr 0 c.tr cfg

/-! ### Finitely many states -/

/-- **States of a multi-tape code.** The states of a code $c$ for machines with $k$ work tapes
form the finite set of natural numbers consisting of the initial state $0$ and the next state of
every table entry of $c$ that does not halt. -/
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

/-- **Next states of a code lie in its state set.** For a code $c$, a state $q$, an input symbol
$a$ and work tape symbols $w$, if the action of $c$ at $(q, a, w)$ has a next state $q'$ (rather
than halting), then $q'$ belongs to the set of states of $c$. -/
theorem next_act_mem_states (c : Code k) {q q' : ℕ} {a : Option Bool} {w : Fin k → Option Bool}
    (h : (c.act q a w).next = some q') : q' ∈ c.states := by
  unfold act at h
  cases hl : @List.lookup _ _ instBEqOfDecidableEq (q, a, w) c.table with
  | none => simp [hl, CodeAction.halt] at h
  | some e =>
    rw [hl, Option.getD_some] at h
    refine Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_filterMap.mpr ?_))
    exact ⟨_, mem_of_lookup_eq_some hl, h⟩

/-- **Codes denote finite-state machines.** Let $c$ be a code for a machine with $k$ work tapes.
For every binary input $x$ and every number of steps $t$, if the machine of $c$, run for $t$
steps from its initial configuration on $x$, has not halted and is in state $q$, then $q$ lies
in the finite set of states of $c$. -/
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

/-- **Work tapes as zippers.** A work tape is a pair of finite lists of cells, each cell a bit or
blank: the cells left of the head, nearest first, and the cells from the head rightwards; cells
beyond both lists are blank. -/
abbrev Tape := List (Option Bool) × List (Option Bool)

namespace Tape

/-- **Symbol under the head of a zipper tape.** The symbol read from a work tape given as a zipper
$(l, r)$ is the first cell of $r$, or the blank if $r$ is empty. -/
def read (t : Tape) : Option Bool := t.2.headI

/-- **Writing on a zipper tape.** Writing an optional symbol on a work tape leaves the tape
unchanged when no symbol is given; given a symbol $s$ (a bit or blank), it replaces the cell
under the head by $s$ and keeps all other cells. -/
def write : Option (Option Bool) → Tape → Tape
  | none, t => t
  | some s, t => (t.1, s :: t.2.tail)

/-- **Moving the head of a zipper tape.** For a coded move $m$ and a work tape given as a zipper
$(l, r)$: if $m = 0$ the head moves one cell left, removing the first cell of $l$ (the blank if $l$
is empty) and putting it in front of $r$; if $m = 1$ the tape is unchanged; otherwise the head
moves one cell right, removing the first cell of $r$ (the blank if $r$ is empty) and putting it in
front of $l$. -/
def move (m : ℕ) (t : Tape) : Tape :=
  if m = 0 then (t.1.tail, t.1.headI :: t.2)
  else if m = 1 then t
  else (t.2.headI :: t.1, t.2.tail)

/-- **Cell of a zipper tape.** For a work tape $t$ in zipper form and an integer $j$, the cell of
$t$ at $j$ is the symbol at offset $j$ from the head: for $j = n \ge 0$ it is entry $n$ (counting
from $0$) of the list of cells from the head rightwards, and for $j = -(n + 1)$ it is entry $n$ of
the list of cells left of the head, nearest first; in either case it is the blank when the list
has no entry $n$. -/
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

/-- **Explicit configurations of the code evaluator.** An explicit configuration for a machine
with $k$ work tapes consists of an optional state in $\mathbb{N}$ (none when the machine has
halted); the input head position, a natural number shifted by one, so that position $0$ is the
cell left of the input; the $k$ work tapes, each a zipper (the cells left of the head, nearest
first, and the cells from the head rightwards, all further cells blank); and the output written
so far, a binary word. -/
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

/-- **Explicit configurations as tuples.** The bijection between explicit configurations and
tuples $(q, p, t, o)$ that sends a configuration to its optional state $q$ (empty when halted),
its shifted input head position $p \in \mathbb{N}$, its family $t$ of $k$ work tapes (each a
zipper) and its output $o$ so far, a list of bits. -/
def equivProd : Config k ≃ Option ℕ × ℕ × (Fin k → Tape) × List Bool where
  toFun e := (e.state, e.inputPos, e.tapes, e.output)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (Config k) := Primcodable.ofEquiv _ equivProd

/-- **Initial configuration of the clocked evaluator.** The initial explicit configuration has
state $0$, the input head on the first input cell (position $1$, positions being shifted by one),
every work tape blank (both halves of its zipper empty), and empty output. -/
def init : Config k := ⟨some 0, 1, fun _ ↦ ([], []), []⟩

/-- **Input symbol under the input head.** For an input $x$ and a shifted input head position
$p$, the input symbol is the blank if $p = 0$; otherwise it is the entry of $x$ at index $p - 1$
(counting from $0$) if $p - 1 < |x|$, and the blank if $p - 1 \ge |x|$. -/
def inputSym (x : List Bool) (p : ℕ) : Option Bool := if p = 0 then none else x[p - 1]?

/-- **Input head move of the clocked evaluator.** For an input of length $n$, a shifted input head
position $p$ and a coded move $m$, the new position is $p - 1$ (truncated at $0$) if $m = 0$, $p$
if $m = 1$, and $\min(p + 1, n + 1)$ otherwise, so a move right never passes position $n + 1$,
one cell beyond the input. -/
def moveInput (n p m : ℕ) : ℕ := if m = 0 then p - 1 else if m = 1 then p else min (p + 1) (n + 1)

/-- **Applying a coded action.** Given an input word $x$, a coded action $a$ and an explicit
configuration $e$, applying $a$ to $e$ gives the configuration whose state is the next state of
$a$; whose input head position is that of $e$, say $p$, moved by the coded input move of $a$,
where a left move gives $p - 1$ (truncated at $0$), staying gives $p$, and a right move gives
$\min(p + 1, |x| + 1)$; whose work tape $i$ is work tape $i$ of $e$ after writing the optional
symbol of $a$ for tape $i$ under the head and then moving the head by the coded move of $a$ for
tape $i$; and whose output is the output of $e$ followed by the output bit of $a$, if any. -/
def apply (x : List Bool) (a : CodeAction k) (e : Config k) : Config k where
  state := a.next
  inputPos := moveInput x.length e.inputPos a.inputMove
  tapes i := Tape.move (a.work i).2 (Tape.write (a.work i).1 (e.tapes i))
  output := e.output ++ a.out.toList

/-- **Evaluator step.** One step of the evaluator for a code $c$ on a binary input $x$ leaves an
explicit configuration $e$ unchanged if $e$ has halted; if $e$ is in state $q$, it applies to
$e$ the coded action of $c$ at $q$, the input symbol at the input head position of $e$ and the
symbols under the heads of the work tapes of $e$. -/
def step (c : Code k) (x : List Bool) (e : Config k) : Config k :=
  match e.state with
  | none => e
  | some q => e.apply x (c.act q (inputSym x e.inputPos) fun i ↦ (e.tapes i).read)

end Config

/-- **Clocked evaluator.** The clocked evaluator runs a code $c$ on a binary input $x$ for $T$
steps: it applies the evaluator's step $T$ times to the initial explicit configuration. If the
resulting configuration is halted, it returns that configuration's output; otherwise it
returns no result. -/
def evalSteps (c : Code k) (x : List Bool) (T : ℕ) : Option (List Bool) :=
  match ((Config.step c x)^[T] Config.init).state with
  | none => some ((Config.step c x)^[T] Config.init).output
  | some _ => none

/-! ### Agreement with CSLib's semantics -/

/-- **Explicit configurations representing machine configurations.** An explicit configuration $e$
represents a configuration $C$ of CSLib's multi-tape model on input $x$ when they have the same
state, the same shifted input head position and the same output, and for every work tape $i$ and
every cell $z \in \mathbb{Z}$, the content of cell $z$ of tape $i$ in $C$ equals the cell of tape
$i$ of $e$ at offset $z - p_i$ from its head, where $p_i$ is the head position of tape $i$
in $C$. -/
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

/-- **The evaluator simulates the machine step for step.** Let $c$ be a code and $x$ a binary
input. If an explicit configuration $e$ represents a configuration $C$ of the machine of $c$ on
$x$, then the evaluator's step of $e$ for $c$ on $x$ represents the successor of $C$ under the
machine of $c$. -/
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

/-- **The evaluator tracks the machine run.** For a code $c$, an input $x$ and every $t$, the
explicit configuration obtained from the initial one by $t$ steps of the evaluator for $c$ on $x$
represents the configuration that the machine of $c$ reaches after $t$ steps from its initial
configuration on $x$. -/
theorem represents_iterate (c : Code k) (x : List Bool) (t : ℕ) :
    Represents ((Config.step c x)^[t] Config.init) (c.toTM.runFrom (c.toTM.initCfg x) t) := by
  induction t with
  | zero => exact represents_init c x
  | succ t ih =>
    rw [Function.iterate_succ_apply', MultiTapeTM.runFrom_succ]
    exact ih.step c

/-- **Evaluator agreement.** For every code $c$, binary input $x$, clock $T \in \mathbb{N}$
and binary word $o$, the clocked evaluator of $c$ on $x$ with clock $T$ returns $o$ if and
only if the machine of $c$, run for $T$ steps from its initial configuration on $x$, has
halted and its output is $o$. -/
theorem evalSteps_eq_some_iff (c : Code k) (x : List Bool) (T : ℕ) (o : List Bool) :
    c.evalSteps x T = some o ↔
      (c.toTM.runFrom (c.toTM.initCfg x) T).Halted ∧
        (c.toTM.runFrom (c.toTM.initCfg x) T).output = o := by
  have h := represents_iterate c x T
  unfold evalSteps
  simp only [Cfg.Halted, ← h.state, ← h.output]
  cases ((Config.step c x)^[T] Config.init).state <;> simp

/-- **The evaluator returns within the clock exactly when the machine runs in time.** For a code
$c$, an input $x$ and a clock $T$, the clocked evaluator of $c$ on $x$ with clock $T$ returns an
output if and only if the machine of $c$ runs in time $T$ on $x$, that is, every computation path
of that machine on $x$ with at least $T$ steps ends in a halted configuration. -/
theorem isSome_evalSteps_iff_runsInTime (c : Code k) (x : List Bool) (T : ℕ) :
    (c.evalSteps x T).isSome ↔ c.toTM.RunsInTime x T := by
  rw [runsInTime_iff_halted, Option.isSome_iff_exists]
  simp only [evalSteps_eq_some_iff]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨_, h, rfl⟩⟩

/-- **Monotonicity of the clocked evaluator for multi-tape codes.** For a code $c$ for machines
with $k$ work tapes, a binary input $x$, a binary word $o$ and clocks $T \le T'$ in $\mathbb{N}$,
if the clocked evaluator of $c$ on $x$ returns $o$ with clock $T$, then it also returns $o$ with
clock $T'$. -/
theorem evalSteps_mono (c : Code k) {x : List Bool} {T T' : ℕ} {o : List Bool}
    (h : c.evalSteps x T = some o) (hT : T ≤ T') : c.evalSteps x T' = some o := by
  rw [evalSteps_eq_some_iff] at h ⊢
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ hT h.1]
  exact h

/-- **A code computes exactly what its clocked evaluator returns.** For a code $c$ with $k$ work
tapes and binary words $x$ and $o$, the machine of $c$ computes $o$ on input $x$, that is, it
eventually halts on $x$ with output $o$, if and only if there is a clock $T \in \mathbb{N}$ such
that the clocked evaluator of $c$ run on $x$ for $T$ steps returns $o$. -/
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
