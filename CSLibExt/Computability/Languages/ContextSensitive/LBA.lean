/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextSensitive.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Relation

/-!
# Linear bounded automata and context-sensitive grammars

A **linear bounded automaton** (LBA) is a nondeterministic Turing machine whose
tape is the input word itself: the head never leaves the `n` cells of the input
of length `n`. This file defines that model, and the grammar construction of
the theorem that a language is context-sensitive iff some LBA recognizes it
(Sipser, Section 5.1; Hopcroft-Motwani-Ullman, Section 11.1).

The machine observes the tape boundaries: its transition function sees not
only the symbol under the head but also whether the head is on the first
cell, the last cell, both (a one-cell tape), or neither. Without this the
model could not recognize general context-sensitive languages: a machine
blind to the boundaries has every accepting run on `w` replay unchanged
on every `w ++ v`, so its language would be closed under right extension
(a `[true]`-only language is then impossible). The grammar cells below
carry the same boundary tag, which the conversion rules discard.

Two warnings about the statement, both of which the formalization is built
around:

* The LBA is **nondeterministic**. Sipser and Hopcroft-Motwani-Ullman define
  it so, and the context-sensitive languages are the nondeterministic
  linear-space languages. The deterministic linear-space languages are a
  different class: whether deterministic and nondeterministic linear space
  coincide is open (Savitch's theorem only gives nondeterministic linear
  space inside deterministic quadratic space). In particular, nothing here
  claims that a context-sensitive language is accepted by a *deterministic*
  linear-space machine. CSLib's `SingleTapeTM.IsLBA` (in
  `CSLibExt/Computability/Machines/Turing/SingleTape/SpaceBounded.lean`) is the
  deterministic restriction; its halting set is decidable there, and the
  fenced machines of `Fence.lean` are deterministic LBAs.
* The context-sensitive grammars of
  `CSLibExt/Computability/Languages/ContextSensitive/Basic.lean` have no
  `S → ε` exception, so they generate no empty word. The LBA below may
  accept the empty word (if its initial state is accepting). The equivalence
  is therefore stated for nonempty words.

The grammar construction is the textbook one. A sentential form is a list of
cells, one per input cell. A cell records the **original** input symbol
(which never changes, and which the cell becomes on conversion), the
**current** tape symbol (which the machine may overwrite), the head state if
the head is on this cell, whether the cell is **active**, and its
**boundary tag**. Generation produces inactive cells and a trailing
generator; activation switches cells on one by one; simulation rewrites
one or two active cells at the head exactly as the machine steps, using
the head cell's boundary tag to select the transition; conversion turns
an active cell into its original terminal, the head cell only in the
accepting state, discarding the boundary tag. The original symbol is what
makes conversion use the input symbol: a cell the machine overwrote
still converts to the input symbol it started as.

What is proved here:

* `lbaGrammar_contextSensitive`: the grammar of an LBA is context-sensitive.
* `lba_accepts_implies_grammar_derives`: if the LBA accepts a nonempty word,
  the grammar derives it. This is one inclusion of the LBA-to-grammar
  direction (every LBA language, minus the empty word, is contained in a
  context-sensitive language).

The other inclusion of that direction (if the grammar derives a nonempty
word, the LBA accepts it, so the two languages are equal), the converse
direction (every context-sensitive grammar has an LBA recognizing it, the
reverse-derivation LBA), and context-sensitive membership decidability and
its PSPACE bound, are not proved here.
No soundness invariant for the grammar is claimed here: an earlier
version of this file stated one (`lbaInv`), but it was not preserved
by the grammar rules (a terminal form could satisfy it without the
tracked configuration being accepting, and simulation interleaved
with generation could move the tracked configuration past what the
generation branch allowed), so it was removed rather than kept as an
unproved claim.

## Main definitions

- `Cslib.Language.LBAMove`, `Cslib.Language.LinearBoundedAutomaton`,
  `Cslib.Language.LBAConfig`: the move, the machine, and its configurations.
- `Cslib.Language.LinearBoundedAutomaton.Accepts`,
  `Cslib.Language.LinearBoundedAutomaton.language`: acceptance and language.
- `Cslib.Language.LBANT`, `Cslib.Language.lbaGrammar`: the grammar
  nonterminals and the grammar of an LBA.
- `Cslib.Language.encodeCfg`: a configuration as a sentential form.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage,
  2013, §5.1 (linear bounded automata; the definition, the equivalence with
  context-sensitive grammars, and Theorem 5.9, decidability of `A_LBA`).
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory,
  Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1 (the
  equivalence of context-sensitive languages and linear bounded automata).
-/

@[expose] public section

namespace Cslib
namespace Language

variable {Q Γ : Type*}

/-! ### The nondeterministic linear bounded automaton -/

/-- Where the head sits relative to the tape boundaries: strictly inside
the tape, on the first cell, on the last cell, or on the only cell of a
one-cell tape. The transition function observes this tag, so the machine
can tell the two ends of its tape apart from interior cells. -/
inductive LBABoundary where
  /-- Strictly inside the tape: not the first and not the last cell. -/
  | middle : LBABoundary
  /-- On the first cell of a tape of length at least two. -/
  | left : LBABoundary
  /-- On the last cell of a tape of length at least two. -/
  | right : LBABoundary
  /-- On the only cell of a one-cell tape. -/
  | both : LBABoundary
  deriving DecidableEq

/-- The finite type of boundary tags. -/
instance : Fintype LBABoundary where
  elems := {LBABoundary.middle, LBABoundary.left, LBABoundary.right, LBABoundary.both}
  complete := by intro x; cases x <;> simp

/-- The boundary tag of head position `h` on a tape of length `n`. -/
def LBABoundary.ofHead (h n : ℕ) : LBABoundary :=
  if h = 0 then (if n = 1 then .both else .left)
  else if h + 1 = n then .right else .middle

/-- The boundary tag at the head of a one-cell tape. -/
theorem LBABoundary.ofHead_eq_both {h n : ℕ} (h0 : h = 0) (hn : n = 1) :
    LBABoundary.ofHead h n = .both := by
  simp [LBABoundary.ofHead, h0, hn]

/-- The boundary tag at the head of the first cell of a longer tape. -/
theorem LBABoundary.ofHead_eq_left {h n : ℕ} (h0 : h = 0) (hn : n ≠ 1) :
    LBABoundary.ofHead h n = .left := by
  simp [LBABoundary.ofHead, h0, hn]

/-- The boundary tag at the head of the last cell of a longer tape. -/
theorem LBABoundary.ofHead_eq_right {h n : ℕ} (h0 : h ≠ 0) (hn : h + 1 = n) :
    LBABoundary.ofHead h n = .right := by
  simp [LBABoundary.ofHead, h0, hn]

/-- The boundary tag at an interior head position. -/
theorem LBABoundary.ofHead_eq_middle {h n : ℕ} (h0 : h ≠ 0) (hn : h + 1 ≠ n) :
    LBABoundary.ofHead h n = .middle := by
  simp [LBABoundary.ofHead, h0, hn]

/-- A head move of a linear bounded automaton: left, stay, or right. -/
inductive LBAMove where
  /-- Move the head one cell to the left. -/
  | left : LBAMove
  /-- Leave the head on the same cell. -/
  | stay : LBAMove
  /-- Move the head one cell to the right. -/
  | right : LBAMove
  deriving DecidableEq

/-- The head position after a move: left decrements, stay keeps, right
increments. -/
def LBAMove.moveHead (mv : LBAMove) (h : ℕ) : ℕ :=
  match mv with
  | .left => h - 1
  | .stay => h
  | .right => h + 1

/-- A move is legal from the head position `h` on a tape of length `n` when
the source head is on the tape and the new head position is still on the
tape. In particular a left move from an out-of-bounds head is illegal,
even though the truncated new head `h - 1` would still be out of bounds:
legality requires `h < n` for left moves as well. -/
def LBAMove.legal (mv : LBAMove) (h n : ℕ) : Prop :=
  match mv with
  | .left => 0 < h ∧ h < n
  | .stay => h < n
  | .right => h + 1 < n

/-- A **linear bounded automaton**: a nondeterministic Turing machine whose
tape is the input word. The transition function gives, for a state, the
symbol under the head (`none` for a blank cell), and the boundary tag of
the head position, the finite set of possible next states, symbols to
write (`none` for a blank), and head moves. The boundary tag is what lets
the machine detect the ends of its tape: without it the model could not
recognize general context-sensitive languages. A move that would take
the head off the tape is not a step. -/
structure LinearBoundedAutomaton (Q Γ : Type*) where
  /-- The initial state. -/
  q₀ : Q
  /-- The accepting state. -/
  qAcc : Q
  /-- The transition function: from a state, the symbol under the head,
  and the boundary tag of the head position, the finite set of possible
  (next state, written symbol, head move) triples. -/
  delta : Q → Option Γ → LBABoundary → Finset (Q × Option Γ × LBAMove)

/-- A configuration of a linear bounded automaton: the state, the tape
(a list of cells, one per input cell; `none` is a blank), and the head
position. -/
structure LBAConfig (Q Γ : Type*) where
  /-- The current state. -/
  state : Q
  /-- The tape: one cell per input cell. -/
  tape : List (Option Γ)
  /-- The head position, an index into the tape. -/
  head : ℕ

namespace LinearBoundedAutomaton

variable {M : LinearBoundedAutomaton Q Γ}

/-- The initial configuration on the input `w`: the initial state, the tape
`w` itself (no blanks), the head on the first cell. -/
def initCfg (w : List Γ) : LBAConfig Q Γ :=
  ⟨M.q₀, w.map some, 0⟩

/-- One step of the machine: choose a transition for the current state,
the symbol under the head, and its boundary tag, write the symbol, move
the head legally. A step from a configuration whose head is off the
tape is impossible: legality requires the source head to be on the
tape. -/
def Step (c c' : LBAConfig Q Γ) : Prop :=
  ∃ (q' : Q) (b' : Option Γ) (mv : LBAMove),
    (q', b', mv) ∈
      M.delta c.state (c.tape[c.head]?).join
        (LBABoundary.ofHead c.head c.tape.length) ∧
    c' = ⟨q', c.tape.set c.head b', mv.moveHead c.head⟩ ∧
    mv.legal c.head c.tape.length

/-- `M` **accepts** `w` when some run from the initial configuration on `w`
reaches a configuration in the accepting state. -/
def Accepts (w : List Γ) : Prop :=
  ∃ c : LBAConfig Q Γ, Relation.ReflTransGen M.Step (M.initCfg w) c ∧
    c.state = M.qAcc

/-- The language of `M`: the words it accepts. -/
def language : Set (List Γ) :=
  {w | M.Accepts w}

end LinearBoundedAutomaton

/-! ### The grammar nonterminals -/

/-- The nonterminals of the grammar of an LBA: a cell, a generator, and the
start symbol. A cell records the original input symbol, the current tape
symbol, the head state if the head is on the cell, whether the cell is
active (simulation acts only on active cells), and the boundary tag of
its position (so simulation can apply the boundary-aware transitions). -/
inductive LBANT (Γ Q : Type*) where
  /-- A tape cell: original symbol, current symbol, head state, active,
  boundary tag. -/
  | cell (orig : Γ) (cur : Option Γ) (st : Option Q) (active : Bool)
      (bnd : LBABoundary) : LBANT Γ Q
  /-- The generator: it produces the remaining cells, then disappears. -/
  | gen : LBANT Γ Q
  /-- The start symbol: the initial nonterminal of the grammar. -/
  | start : LBANT Γ Q
  deriving DecidableEq, Fintype

namespace LinearBoundedAutomaton

variable {M : LinearBoundedAutomaton Q Γ} [_instFintypeQ : Fintype Q]
  [_instFintypeG : Fintype Γ] [_instDecidableEqQ : DecidableEq Q]
  [_instDecidableEqG : DecidableEq Γ]

/-- A grammar symbol for the LBA grammar: a cell as a nonterminal. -/
abbrev cellSym (orig : Γ) (cur : Option Γ) (st : Option Q) (active : Bool)
    (bnd : LBABoundary) : Symbol Γ (LBANT Γ Q) :=
  .nonterminal (.cell orig cur st active bnd)

/-- The start symbol as a grammar symbol. -/
abbrev startSym : Symbol Γ (LBANT Γ Q) :=
  .nonterminal .start

/-- The generator as a grammar symbol. -/
abbrev genSym : Symbol Γ (LBANT Γ Q) :=
  .nonterminal .gen

/-- A terminal symbol of the grammar. -/
abbrev termSym (a : Γ) : Symbol Γ (LBANT Γ Q) :=
  .terminal a

/-! ### The grammar rules -/

/-- The generation rules: the start symbol produces the first cell and the
generator (or, for a one-cell word, the first cell alone, tagged `both`);
the generator produces a middle non-head cell and itself, or a final
right non-head cell. The first cell of a longer word is tagged `left`. -/
noncomputable def genRules (M : LinearBoundedAutomaton Q Γ) : List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList : List Γ).flatMap fun a ↦
    [([startSym (Γ := Γ) (Q := Q)],
       [cellSym a (some a) (some M.q₀) false .left, genSym]),
     ([startSym (Γ := Γ) (Q := Q)],
       [cellSym a (some a) (some M.q₀) false .both]),
     ([genSym (Γ := Γ) (Q := Q)],
       [cellSym a (some a) none false .middle, genSym]),
     ([genSym (Γ := Γ) (Q := Q)],
       [cellSym a (some a) none false .right])]

/-- The activation rules: an inactive cell becomes active, keeping its
original, current, head state, and boundary tag. -/
noncomputable def activateRules :
    List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList : List (Γ × Option Γ × Option Q × LBABoundary)).flatMap
    fun ⟨a, cur, st, bnd⟩ ↦
      [([cellSym a cur st false bnd], [cellSym a cur st true bnd])]

/-- The simulation rules for a stay move: the head cell rewrites its current
symbol and state, staying active, keeping its boundary tag. -/
noncomputable def simStayRules (M : LinearBoundedAutomaton Q Γ) :
    List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList : List (Q × Option Γ × Γ × LBABoundary)).flatMap
    fun ⟨q, read, orig, bnd⟩ ↦
      ((M.delta q read bnd).toList).flatMap fun ⟨q', write, mv⟩ ↦
        match mv with
        | .stay => [([cellSym orig read (some q) true bnd],
            [cellSym orig write (some q') true bnd])]
        | _ => []

/-- The simulation rules for a right move: the head cell rewrites its current
symbol and loses the head; the neighbouring cell gains the head. Both cells
keep their boundary tags. -/
noncomputable def simRightRules (M : LinearBoundedAutomaton Q Γ) :
    List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList :
      List (Q × Option Γ × Γ × Γ × Option Γ × LBABoundary × LBABoundary)).flatMap
    fun ⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩ ↦
      ((M.delta q read bnd).toList).flatMap fun ⟨q', write, mv⟩ ↦
        match mv with
        | .right => [([cellSym orig read (some q) true bnd,
              cellSym orig₂ cur₂ none true bnd₂],
            [cellSym orig write none true bnd,
              cellSym orig₂ cur₂ (some q') true bnd₂])]
        | _ => []

/-- The simulation rules for a left move: the neighbouring cell gains the head;
the head cell rewrites its current symbol and loses the head. Both cells
keep their boundary tags. -/
noncomputable def simLeftRules (M : LinearBoundedAutomaton Q Γ) :
    List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList :
      List (Q × Option Γ × Γ × Γ × Option Γ × LBABoundary × LBABoundary)).flatMap
    fun ⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩ ↦
      ((M.delta q read bnd).toList).flatMap fun ⟨q', write, mv⟩ ↦
        match mv with
        | .left => [([cellSym orig₂ cur₂ none true bnd₂,
              cellSym orig read (some q) true bnd],
            [cellSym orig₂ cur₂ (some q') true bnd₂,
              cellSym orig write none true bnd])]
        | _ => []

/-- The conversion rules: an active cell becomes its original terminal. The
head cell converts only in the accepting state, so a terminal word is
produced only from an accepting configuration. The boundary tag is
discarded on conversion. -/
noncomputable def convRules (M : LinearBoundedAutomaton Q Γ) :
    List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  (Finset.univ.toList : List (Γ × Option Γ × LBABoundary)).flatMap
    fun ⟨a, cur, bnd⟩ ↦
      [([cellSym a cur (some M.qAcc) true bnd], [termSym a]),
       ([cellSym a cur none true bnd], [termSym a])]

/-- All the rules of the grammar. -/
noncomputable def allRules (M : LinearBoundedAutomaton Q Γ) : List (List (Symbol Γ (LBANT Γ Q)) × List (Symbol Γ (LBANT Γ Q))) :=
  genRules M ++ activateRules ++ simStayRules M ++ simRightRules M ++
    simLeftRules M ++ convRules M

/-- **The grammar of an LBA**: the grammar whose rules are the generation,
activation, simulation, and conversion rules above, starting from the start
symbol. -/
noncomputable def lbaGrammar (M : LinearBoundedAutomaton Q Γ) : CSGrammar Γ (LBANT Γ Q) where
  rules := allRules M
  initial := .start

/-- The first generation rule is a rule of the grammar. -/
theorem mem_genRules_start (a : Γ) :
    ([startSym (Γ := Γ) (Q := Q)],
      [cellSym a (some a) (some M.q₀) false .left, genSym (Γ := Γ) (Q := Q)]) ∈
      M.genRules := by
  simp [genRules]

/-- **The grammar of an LBA is context-sensitive**: every production has a
nonterminal on its left side and does not shrink. -/
theorem lbaGrammar_contextSensitive : IsContextSensitive M.lbaGrammar := by
  intro r hr
  rw [lbaGrammar, allRules] at hr
  obtain hr | hconv := List.mem_append.mp hr
  · obtain hr | hleft := List.mem_append.mp hr
    · obtain hr | hright := List.mem_append.mp hr
      · obtain hr | hstay := List.mem_append.mp hr
        · obtain hgen | hact := List.mem_append.mp hr
          · rw [genRules, List.mem_flatMap] at hgen
            obtain ⟨a, -, hgen⟩ := hgen
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
              at hgen
            rcases hgen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp [Symbol.isNonterminal]
          · rw [activateRules, List.mem_flatMap] at hact
            obtain ⟨⟨a, cur, st, bnd⟩, -, hact⟩ := hact
            rw [List.mem_singleton] at hact
            obtain ⟨rfl, rfl⟩ := hact
            simp [Symbol.isNonterminal]
        · rw [simStayRules, List.mem_flatMap] at hstay
          obtain ⟨⟨q, read, orig, bnd⟩, -, hstay⟩ := hstay
          rw [List.mem_flatMap] at hstay
          obtain ⟨⟨q', write, mv⟩, -, hstay⟩ := hstay
          cases mv with
          | stay =>
            rw [List.mem_singleton] at hstay
            obtain ⟨rfl, rfl⟩ := hstay
            simp [Symbol.isNonterminal]
          | left => simp at hstay
          | right => simp at hstay
      · rw [simRightRules, List.mem_flatMap] at hright
        obtain ⟨⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩, -, hright⟩ := hright
        rw [List.mem_flatMap] at hright
        obtain ⟨⟨q', write, mv⟩, -, hright⟩ := hright
        cases mv with
        | left => simp at hright
        | stay => simp at hright
        | right =>
          rw [List.mem_singleton] at hright
          obtain ⟨rfl, rfl⟩ := hright
          simp [Symbol.isNonterminal]
    · rw [simLeftRules, List.mem_flatMap] at hleft
      obtain ⟨⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩, -, hleft⟩ := hleft
      rw [List.mem_flatMap] at hleft
      obtain ⟨⟨q', write, mv⟩, -, hleft⟩ := hleft
      cases mv with
      | left =>
        rw [List.mem_singleton] at hleft
        obtain ⟨rfl, rfl⟩ := hleft
        simp [Symbol.isNonterminal]
      | stay => simp at hleft
      | right => simp at hleft
  · rw [convRules, List.mem_flatMap] at hconv
    obtain ⟨⟨a, cur, bnd⟩, -, hconv⟩ := hconv
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hconv
    rcases hconv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Symbol.isNonterminal]

/-! ### Configurations as sentential forms -/

/-- The cells of a configuration, as a list of cell tuples: original symbol,
current symbol, head state, active, boundary tag. The head is given as
`some i` for the head position, or `none` once it has been passed. The
`start` index is the position of the first cell in the whole word and
`total` is the whole word's length, so the boundary tag of the cell at
offset `j` is `ofHead (start + j) total`. -/
def encodeCellsAux : List Γ → List (Option Γ) → Option ℕ → Q → ℕ → ℕ →
    List (Γ × Option Γ × Option Q × Bool × LBABoundary)
  | [], _, _, _, _, _ => []
  | _ :: _, [], _, _, _, _ => []
  | a :: w, cur :: tape, some 0, q, i, total =>
      (a, cur, some q, true, LBABoundary.ofHead i total) ::
        encodeCellsAux w tape none q (i + 1) total
  | a :: w, cur :: tape, some (k + 1), q, i, total =>
      (a, cur, none, true, LBABoundary.ofHead i total) ::
        encodeCellsAux w tape (some k) q (i + 1) total
  | a :: w, cur :: tape, none, q, i, total =>
      (a, cur, none, true, LBABoundary.ofHead i total) ::
        encodeCellsAux w tape none q (i + 1) total

/-- A cell tuple as a grammar symbol. -/
def cellTupleSym : Γ × Option Γ × Option Q × Bool × LBABoundary →
    Symbol Γ (LBANT Γ Q)
  | ⟨orig, cur, st, active, bnd⟩ => cellSym orig cur st active bnd

/-- A configuration as a sentential form: the cells of its tape, with the
original symbols taken from the input word `w`. -/
def encodeCfg (_M : LinearBoundedAutomaton Q Γ) (w : List Γ) (cfg : LBAConfig Q Γ) :
    List (Symbol Γ (LBANT Γ Q)) :=
  (encodeCellsAux w cfg.tape (if cfg.head < w.length then some cfg.head else none)
    cfg.state 0 w.length).map cellTupleSym

/-- The middle non-head generated cells of a word, inactive: the cells the
generator produces while the generator remains. -/
def tailCellsMid : List Γ → List (Γ × Option Γ × Option Q × Bool × LBABoundary)
  | [] => []
  | a :: w => (a, some a, none, false, .middle) :: tailCellsMid w

/-- The non-head generated cells of a word, inactive, as the tail of a
generated word: middle cells and a final right cell. -/
def tailCells : List Γ → List (Γ × Option Γ × Option Q × Bool × LBABoundary)
  | [] => []
  | [a] => [(a, some a, none, false, .right)]
  | a :: b :: w => (a, some a, none, false, .middle) :: tailCells (b :: w)

/-- The generated cells of a word, inactive, with the head state on the first
cell: the sentential form generation produces. The first cell is tagged
`both` for a one-cell word and `left` otherwise; the tail is `tailCells`. -/
def genCells (M : LinearBoundedAutomaton Q Γ) :
    List Γ → List (Γ × Option Γ × Option Q × Bool × LBABoundary)
  | [] => []
  | [a] => [(a, some a, some M.q₀, false, .both)]
  | a :: b :: w => (a, some a, some M.q₀, false, .left) :: tailCells (b :: w)

/-- The generated sentential form of a word. -/
def genEncode (M : LinearBoundedAutomaton Q Γ) (w : List Γ) :
    List (Symbol Γ (LBANT Γ Q)) :=
  (genCells (M := M) w).map cellTupleSym

/-- The non-head generated sentential form of a word. -/
def tailEncode (_M : LinearBoundedAutomaton Q Γ) (w : List Γ) :
    List (Symbol Γ (LBANT Γ Q)) :=
  (tailCells w).map cellTupleSym

/-- The middle non-head generated sentential form of a word: every cell
tagged `middle`, for the generator's intermediate stage. -/
def tailEncodeMid (_M : LinearBoundedAutomaton Q Γ) (w : List Γ) :
    List (Symbol Γ (LBANT Γ Q)) :=
  (tailCellsMid w).map cellTupleSym

/-! ### Lemmas about the encoding -/

/-- The encoding has as many cells as the input word, when the tape has the
same length. -/
theorem length_encodeCellsAux {w : List Γ} {tape : List (Option Γ)} {h : Option ℕ} {q : Q}
    {start total : ℕ} (hl : w.length = tape.length) :
    (encodeCellsAux w tape h q start total).length = w.length := by
  induction w generalizing tape h start with
  | nil => rfl
  | cons a w ih =>
    cases tape with
    | nil => simp at hl
    | cons cur tape =>
      simp only [List.length_cons] at hl
      have hl' : w.length = tape.length := Nat.succ.inj hl
      cases h with
      | none => simp only [encodeCellsAux, List.length_cons, ih hl']
      | some n =>
        cases n with
        | zero => simp only [encodeCellsAux, List.length_cons, ih hl']
        | succ n => simp only [encodeCellsAux, List.length_cons, ih hl']

/-- The `i`-th cell of the encoding: original `w[i]`, current `tape[i]`,
head state exactly at the head position, boundary tag of position
`start + i` in a word of length `total`. -/
theorem getElem_encodeCellsAux {w : List Γ} {tape : List (Option Γ)} {h : Option ℕ} {q : Q}
    {start total i : ℕ} (hl : w.length = tape.length) (hi : i < w.length) :
    (encodeCellsAux w tape h q start total)[i]'
        (by rw [length_encodeCellsAux hl]; exact hi) =
      (w[i]'hi, (tape[i]?).join, if h = some i then some q else none, true,
        LBABoundary.ofHead (start + i) total) := by
  induction w generalizing tape h start i with
  | nil => simp at hi
  | cons a w ih =>
    cases tape with
    | nil => simp at hl
    | cons cur tape =>
      simp only [List.length_cons] at hl
      have hl' : w.length = tape.length := Nat.succ.inj hl
      cases i with
      | zero =>
        cases h with
        | none => simp [encodeCellsAux]
        | some n =>
          cases n with
          | zero => simp [encodeCellsAux]
          | succ n => simp [encodeCellsAux]
      | succ i =>
        have hEq : start + (i + 1) = (start + 1) + i := by omega
        cases h with
        | none =>
          have hIH := ih (tape := tape) (h := none) (start := start + 1) (i := i) hl' (by
            simp only [List.length_cons] at hi; omega)
          rw [← hEq] at hIH
          simp only [encodeCellsAux, List.getElem_cons_succ] at hIH ⊢
          rw [hIH]
          simp
        | some n =>
          cases n with
          | zero =>
            have hIH := ih (tape := tape) (h := none) (start := start + 1) (i := i) hl' (by
              simp only [List.length_cons] at hi; omega)
            rw [← hEq] at hIH
            simp only [encodeCellsAux, List.getElem_cons_succ] at hIH ⊢
            rw [hIH]
            simp
          | succ n =>
            have hIH := ih (tape := tape) (h := some n) (start := start + 1) (i := i) hl' (by
              simp only [List.length_cons] at hi; omega)
            rw [← hEq] at hIH
            simp only [encodeCellsAux, List.getElem_cons_succ] at hIH ⊢
            rw [hIH]
            simp only [Option.some.injEq, Nat.succ.injEq, List.getElem?_cons_succ]

/-- One grammar step replacing a block: if `u` splits as `p ++ lhs ++ q`
and `(lhs, rhs)` is a rule, then `u` derives `p ++ rhs ++ q`. -/
theorem derives_replace_list {u p q lhs rhs : List (Symbol Γ (LBANT Γ Q))}
    (hu : u = p ++ lhs ++ q) (hrule : (lhs, rhs) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u (p ++ rhs ++ q) := by
  subst hu
  exact Cslib.Decidability.Rewriting.Derives.single
    (Cslib.Decidability.Rewriting.Step.mk p q (by simpa [lbaGrammar] using hrule))

/-- One grammar step replacing a single cell by a single cell. -/
theorem derives_single_cell {u p q : List (Symbol Γ (LBANT Γ Q))}
    {x y : Symbol Γ (LBANT Γ Q)} (hu : u = p ++ [x] ++ q)
    (hrule : ([x], [y]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u (p ++ [y] ++ q) :=
  derives_replace_list hu hrule

/-- One grammar step replacing two consecutive cells. -/
theorem derives_two_cells {u p q : List (Symbol Γ (LBANT Γ Q))}
    {x₁ x₂ y₁ y₂ : Symbol Γ (LBANT Γ Q)} (hu : u = p ++ [x₁, x₂] ++ q)
    (hrule : ([x₁, x₂], [y₁, y₂]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u (p ++ [y₁, y₂] ++ q) :=
  derives_replace_list hu hrule

/-- A singleton-to-singleton production is a derivation step. -/
theorem derives_singleton_cell {x y : Symbol Γ (LBANT Γ Q)}
    (hrule : ([x], [y]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar [x] [y] :=
  derives_replace_list (u := [x]) (p := []) (q := []) (lhs := [x]) (rhs := [y])
    (hu := by rfl) hrule

/-- A derivation may be appended on the left. -/
theorem derives_append_left {u v : List (Symbol Γ (LBANT Γ Q))}
    (p : List (Symbol Γ (LBANT Γ Q))) (h : Derives M.lbaGrammar u v) :
    Derives M.lbaGrammar (p ++ u) (p ++ v) :=
  Cslib.Decidability.Rewriting.Derives.append_left h p

/-- A derivation may be appended on the right. -/
theorem derives_append_right {u v : List (Symbol Γ (LBANT Γ Q))}
    (p : List (Symbol Γ (LBANT Γ Q))) (h : Derives M.lbaGrammar u v) :
    Derives M.lbaGrammar (u ++ p) (v ++ p) :=
  Cslib.Decidability.Rewriting.Derives.append_right h p

/-- Derivations compose under append. -/
theorem derives_append {a b c d : List (Symbol Γ (LBANT Γ Q))}
    (h₁ : Derives M.lbaGrammar a b) (h₂ : Derives M.lbaGrammar c d) :
    Derives M.lbaGrammar (a ++ c) (b ++ d) :=
  Cslib.Decidability.Rewriting.Derives.append h₁ h₂

/-- Derivations are transitive. -/
theorem derives_trans {a b c : List (Symbol Γ (LBANT Γ Q))}
    (h₁ : Derives M.lbaGrammar a b) (h₂ : Derives M.lbaGrammar b c) :
    Derives M.lbaGrammar a c :=
  Cslib.Decidability.Rewriting.Derives.trans h₁ h₂

/-! ### Rule membership -/

/-- The first generation rule is a rule of the grammar. -/
theorem mem_rule_gen_start (a : Γ) :
    ([startSym (Γ := Γ) (Q := Q)],
      [cellSym a (some a) (some M.q₀) false .left, genSym (Γ := Γ) (Q := Q)]) ∈
      M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, genRules]

/-- The one-cell generation rule is a rule of the grammar. -/
theorem mem_rule_gen_single (a : Γ) :
    ([startSym (Γ := Γ) (Q := Q)],
      [cellSym a (some a) (some M.q₀) false .both]) ∈
      M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, genRules]

/-- The generator step rule is a rule of the grammar. -/
theorem mem_rule_gen_step (a : Γ) :
    ([genSym (Γ := Γ) (Q := Q)],
      [cellSym a (some a) none false .middle, genSym (Γ := Γ) (Q := Q)]) ∈
      M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, genRules]

/-- The final generation rule is a rule of the grammar. -/
theorem mem_rule_gen_last (a : Γ) :
    ([genSym (Γ := Γ) (Q := Q)], [cellSym a (some a) none false .right]) ∈
      M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, genRules]

/-- The activation rule is a rule of the grammar. -/
theorem mem_rule_activate (a : Γ) (cur : Option Γ) (st : Option Q)
    (bnd : LBABoundary) :
    ([cellSym a cur st false bnd], [cellSym a cur st true bnd]) ∈
      M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, activateRules]

/-- A stay transition gives a simulation rule. -/
theorem mem_rule_sim_stay {q q' : Q} {read write : Option Γ} {orig : Γ}
    {bnd : LBABoundary}
    (h : (q', write, LBAMove.stay) ∈ M.delta q read bnd) :
    ([cellSym orig read (some q) true bnd],
      [cellSym orig write (some q') true bnd]) ∈
      M.lbaGrammar.rules := by
  simp only [lbaGrammar, allRules]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  rw [simStayRules]
  apply List.mem_flatMap.mpr
  refine ⟨⟨q, read, orig, bnd⟩, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨⟨q', write, LBAMove.stay⟩, Finset.mem_toList.mpr h, by simp⟩

/-- A right transition gives a simulation rule. -/
theorem mem_rule_sim_right {q q' : Q} {read write : Option Γ} {orig orig₂ : Γ}
    {cur₂ : Option Γ} {bnd bnd₂ : LBABoundary}
    (h : (q', write, LBAMove.right) ∈ M.delta q read bnd) :
    ([cellSym orig read (some q) true bnd, cellSym orig₂ cur₂ none true bnd₂],
      [cellSym orig write none true bnd, cellSym orig₂ cur₂ (some q') true bnd₂]) ∈
      M.lbaGrammar.rules := by
  simp only [lbaGrammar, allRules]
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  rw [simRightRules]
  apply List.mem_flatMap.mpr
  refine ⟨⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩,
    Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨⟨q', write, LBAMove.right⟩, Finset.mem_toList.mpr h, by simp⟩

/-- A left transition gives a simulation rule. -/
theorem mem_rule_sim_left {q q' : Q} {read write : Option Γ} {orig orig₂ : Γ}
    {cur₂ : Option Γ} {bnd bnd₂ : LBABoundary}
    (h : (q', write, LBAMove.left) ∈ M.delta q read bnd) :
    ([cellSym orig₂ cur₂ none true bnd₂, cellSym orig read (some q) true bnd],
      [cellSym orig₂ cur₂ (some q') true bnd₂, cellSym orig write none true bnd]) ∈
      M.lbaGrammar.rules := by
  simp only [lbaGrammar, allRules]
  apply List.mem_append_left
  apply List.mem_append_right
  rw [simLeftRules]
  apply List.mem_flatMap.mpr
  refine ⟨⟨q, read, orig, orig₂, cur₂, bnd, bnd₂⟩,
    Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨⟨q', write, LBAMove.left⟩, Finset.mem_toList.mpr h, by simp⟩

/-- The accepting conversion rule is a rule of the grammar. -/
theorem mem_rule_conv_acc (a : Γ) (cur : Option Γ) (bnd : LBABoundary) :
    ([cellSym a cur (some M.qAcc) true bnd], [termSym a]) ∈ M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, convRules]

/-- The non-head conversion rule is a rule of the grammar. -/
theorem mem_rule_conv_none (a : Γ) (cur : Option Γ) (bnd : LBABoundary) :
    ([cellSym a cur none true bnd], [termSym a]) ∈ M.lbaGrammar.rules := by
  simp [lbaGrammar, allRules, convRules]

/-! ### Generation and activation -/

/-- The generator derives the middle tail cells followed by itself. -/
theorem derives_gen_tail : ∀ w : List Γ,
    Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)]
      (tailEncodeMid M w ++ [genSym]) := by
  intro w
  induction w with
  | nil => exact Cslib.Decidability.Rewriting.Derives.refl _
  | cons a w ih =>
    have hstep : Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)]
        [cellSym a (some a) none false .middle, genSym (Γ := Γ) (Q := Q)] := by
      apply derives_replace_list (p := []) (q := []) (lhs := [genSym (Γ := Γ) (Q := Q)])
        (rhs := [cellSym a (some a) none false .middle, genSym (Γ := Γ) (Q := Q)])
      · rfl
      · exact mem_rule_gen_step a
    exact derives_trans hstep
      (derives_append_left [cellSym a (some a) none false .middle] ih)

/-- The generator derives the tail cells, ending the generation. -/
theorem derives_gen_tail_last : ∀ w : List Γ, w ≠ [] →
    Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)] (tailEncode M w) := by
  intro w _
  induction w with
  | nil => contradiction
  | cons a w ih =>
    cases w with
    | nil =>
      exact derives_singleton_cell (mem_rule_gen_last a)
    | cons b w =>
      have hstep : Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)]
          [cellSym a (some a) none false .middle, genSym (Γ := Γ) (Q := Q)] := by
        apply derives_replace_list (p := []) (q := []) (lhs := [genSym (Γ := Γ) (Q := Q)])
          (rhs := [cellSym a (some a) none false .middle, genSym (Γ := Γ) (Q := Q)])
        · rfl
        · exact mem_rule_gen_step a
      have ih' : Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)]
          (tailEncode M (b :: w)) := ih (by simp)
      exact derives_trans hstep
        (derives_append_left [cellSym a (some a) none false .middle] ih')

/-- The start symbol derives the generated sentential form of a word. -/
theorem derives_start_genEncode : ∀ w : List Γ, w ≠ [] →
    Derives M.lbaGrammar [startSym (Γ := Γ) (Q := Q)] (genEncode M w) := by
  intro w _
  cases w with
  | nil => contradiction
  | cons a w =>
    cases w with
    | nil =>
      exact derives_singleton_cell (mem_rule_gen_single a)
    | cons b w =>
      have hstep : Derives M.lbaGrammar [startSym (Γ := Γ) (Q := Q)]
          [cellSym a (some a) (some M.q₀) false .left, genSym (Γ := Γ) (Q := Q)] := by
        apply derives_replace_list (p := []) (q := []) (lhs := [startSym (Γ := Γ) (Q := Q)])
          (rhs := [cellSym a (some a) (some M.q₀) false .left, genSym (Γ := Γ) (Q := Q)])
        · rfl
        · exact mem_rule_gen_start a
      have htail : Derives M.lbaGrammar [genSym (Γ := Γ) (Q := Q)]
          (tailEncode M (b :: w)) := derives_gen_tail_last (b :: w) (by simp)
      exact derives_trans hstep
        (derives_append_left [cellSym a (some a) (some M.q₀) false .left] htail)

/-- The tail cells, sitting at offset `start ≥ 1` in a word of total length
`start + w.length`, derive their activated encoding. The offset stays
`≥ 1` in the induction step, so the first tail cell is never tagged
`left`: it is `right` when it is the last cell and `middle` otherwise. -/
theorem derives_tail_activate : ∀ (w : List Γ) (start : ℕ), 1 ≤ start →
    Derives M.lbaGrammar (tailEncode M w)
      ((encodeCellsAux w (w.map some) none M.q₀ start (w.length + start)).map
        cellTupleSym) := by
  intro w
  induction w with
  | nil => intro start _; exact Cslib.Decidability.Rewriting.Derives.refl _
  | cons a w ih =>
    intro start hstart
    cases w with
    | nil =>
      have hbnd : LBABoundary.ofHead start ([a].length + start) = .right := by
        have hlen : [a].length = 1 := rfl
        rw [hlen]
        exact LBABoundary.ofHead_eq_right (by omega) (by omega)
      have htarget : (encodeCellsAux [a] ([a].map some) none M.q₀ start
          ([a].length + start)).map cellTupleSym =
            [cellSym a (some a) none true .right] := by
        simp only [encodeCellsAux, List.map_cons, List.map_nil, hbnd, cellTupleSym]
      rw [htarget]
      exact derives_singleton_cell (mem_rule_activate a (some a) none .right)
    | cons b w =>
      have hpos : 0 < (b :: w).length := by simp
      have hbnd : LBABoundary.ofHead start ((b :: w).length + (start + 1)) = .middle :=
        LBABoundary.ofHead_eq_middle (by omega) (by omega)
      have htarget : (encodeCellsAux (a :: b :: w) ((a :: b :: w).map some) none M.q₀
          start ((a :: b :: w).length + start)).map cellTupleSym =
            [cellSym a (some a) none true .middle] ++
              (encodeCellsAux (b :: w) ((b :: w).map some) none M.q₀ (start + 1)
                ((b :: w).length + (start + 1))).map cellTupleSym := by
        have hlen : (a :: b :: w).length + start = (b :: w).length + (start + 1) := by
          simp only [List.length_cons]; omega
        simp only [encodeCellsAux, List.map_cons, hbnd, cellTupleSym, hlen,
          List.cons_append, List.nil_append]
      rw [htarget]
      have hstep : Derives M.lbaGrammar
          [cellSym a (some a) none false .middle]
          [cellSym a (some a) none true .middle] :=
        derives_singleton_cell (mem_rule_activate a (some a) none .middle)
      exact derives_append hstep (ih (start + 1) (by omega))

/-- The generated form derives the encoding of the initial configuration. -/
theorem derives_gen_activate : ∀ w : List Γ,
    Derives M.lbaGrammar (genEncode M w) (encodeCfg M w (M.initCfg w)) := by
  intro w
  cases w with
  | nil => exact Cslib.Decidability.Rewriting.Derives.refl _
  | cons a w =>
    cases w with
    | nil =>
      have hstep : Derives M.lbaGrammar
          [cellSym a (some a) (some M.q₀) false .both]
          [cellSym a (some a) (some M.q₀) true .both] :=
        derives_singleton_cell (mem_rule_activate a (some a) (some M.q₀) .both)
      have htarget : encodeCfg M [a] (M.initCfg [a]) =
          [cellSym a (some a) (some M.q₀) true .both] := by
        have hbnd : LBABoundary.ofHead 0 1 = .both :=
          LBABoundary.ofHead_eq_both rfl rfl
        simp only [encodeCfg, LinearBoundedAutomaton.initCfg, List.map_cons,
          List.map_nil, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.zero_lt_succ, if_true, encodeCellsAux,
          cellTupleSym, hbnd]
      rw [htarget]
      exact hstep
    | cons b w =>
      have hstep : Derives M.lbaGrammar
          [cellSym a (some a) (some M.q₀) false .left]
          [cellSym a (some a) (some M.q₀) true .left] :=
        derives_singleton_cell (mem_rule_activate a (some a) (some M.q₀) .left)
      have htail : Derives M.lbaGrammar (tailEncode M (b :: w))
          ((encodeCellsAux (b :: w) ((b :: w).map some) none M.q₀ 1
            ((b :: w).length + 1)).map cellTupleSym) :=
        derives_tail_activate (b :: w) 1 (by omega)
      have htarget : encodeCfg M (a :: b :: w) (M.initCfg (a :: b :: w)) =
          [cellSym a (some a) (some M.q₀) true .left] ++
            (encodeCellsAux (b :: w) ((b :: w).map some) none M.q₀ 1
              ((b :: w).length + 1)).map cellTupleSym := by
        rfl
      rw [htarget]
      exact derives_append hstep htail

/-! ### Derivations by setting cells -/

/-- A list splits at two consecutive positions. -/
theorem take_append_two {α : Type*} {l : List α} {i : ℕ} (hi : i + 1 < l.length) :
    l = List.take i l ++ [l[i]'(by omega), l[i + 1]'hi] ++ List.drop (i + 2) l := by
  have h1 : l = List.take i l ++ [l[i]'(by omega)] ++ List.drop (i + 1) l := by
    rw [List.take_append_getElem (by omega : i < l.length), List.take_append_drop]
  have h2 : List.drop (i + 1) l = l[i + 1]'hi :: List.drop (i + 2) l :=
    List.drop_eq_getElem_cons (by omega)
  rw [h2] at h1
  exact h1.trans (by simp only [List.append_assoc, List.cons_append, List.nil_append])

/-- A single-cell replacement that is a production is a derivation step. -/
theorem derives_set_single {u : List (Symbol Γ (LBANT Γ Q))} {i : ℕ}
    {y : Symbol Γ (LBANT Γ Q)} (hi : i < u.length)
    (hrule : ([u[i]'hi], [y]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u (u.set i y) := by
  have hdec : u = List.take i u ++ [u[i]'hi] ++ List.drop (i + 1) u := by
    rw [List.take_append_getElem hi, List.take_append_drop]
  have hset : u.set i y = List.take i u ++ [y] ++ List.drop (i + 1) u := by
    simpa [hi] using List.set_eq_take_append_cons_drop (l := u) (i := i) (a := y)
  rw [hset]
  exact derives_replace_list (p := List.take i u) (q := List.drop (i + 1) u)
    (lhs := [u[i]'hi]) (rhs := [y]) (hu := hdec) hrule

/-- Dropping past a set position is unaffected by the set. -/
theorem drop_set_of_gt {α : Type*} {l : List α} {i : ℕ} {y : α} (hi : i < l.length) :
    List.drop (i + 2) (l.set i y) = List.drop (i + 2) l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ j =>
      change List.drop (j + 2) (l.set j y) = List.drop (j + 2) l
      exact ih (i := j) (by simp only [List.length_cons] at hi; omega)

/-- Taking past a set position keeps the new value at that position. -/
theorem take_set {α : Type*} {l : List α} {i : ℕ} {y : α} (hi : i < l.length) :
    List.take (i + 1) (l.set i y) = List.take i l ++ [y] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ j =>
      change x :: List.take (j + 1) (l.set j y) = (x :: List.take j l) ++ [y]
      rw [ih (i := j) (by simp only [List.length_cons] at hi; omega), List.cons_append]

/-- A two-cell replacement that is a production is a derivation step. -/
theorem derives_set_two {u : List (Symbol Γ (LBANT Γ Q))} {i : ℕ}
    {y₁ y₂ : Symbol Γ (LBANT Γ Q)} (hi : i + 1 < u.length)
    (hrule : ([u[i]'(by omega), u[i + 1]'hi], [y₁, y₂]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u ((u.set i y₁).set (i + 1) y₂) := by
  have hdec : u = List.take i u ++ [u[i]'(by omega), u[i + 1]'hi] ++ List.drop (i + 2) u :=
    take_append_two hi
  have hset : (u.set i y₁).set (i + 1) y₂ =
      List.take i u ++ [y₁, y₂] ++ List.drop (i + 2) u := by
    have h1 : (u.set i y₁).set (i + 1) y₂ =
        List.take (i + 1) (u.set i y₁) ++ [y₂] ++ List.drop (i + 2) (u.set i y₁) := by
      simpa [List.length_set, hi] using
        List.set_eq_take_append_cons_drop (l := u.set i y₁) (i := i + 1) (a := y₂)
    have hdrop : List.drop (i + 2) (u.set i y₁) = List.drop (i + 2) u :=
      drop_set_of_gt (by omega)
    have htake : List.take (i + 1) (u.set i y₁) = List.take i u ++ [y₁] :=
      take_set (by omega)
    rw [h1, hdrop, htake]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hset]
  exact derives_replace_list (p := List.take i u) (q := List.drop (i + 2) u)
    (lhs := [u[i]'(by omega), u[i + 1]'hi]) (rhs := [y₁, y₂]) (hu := hdec) hrule

/-- A two-cell replacement at positions `i` and `j = i + 1`. -/
theorem derives_set_two' {u : List (Symbol Γ (LBANT Γ Q))} {i j : ℕ}
    {y₁ y₂ : Symbol Γ (LBANT Γ Q)} (hi : i + 1 < u.length) (hj : j = i + 1)
    (hrule : ([u[i]'(by omega), u[j]'(by omega)], [y₁, y₂]) ∈ M.lbaGrammar.rules) :
    Derives M.lbaGrammar u ((u.set i y₁).set j y₂) := by
  subst hj
  exact derives_set_two hi hrule

/-! ### Encoding lemmas -/

/-- The encoding of a configuration has as many cells as the input word. -/
theorem length_encodeCfg {w : List Γ} {cfg : LBAConfig Q Γ}
    (hl : cfg.tape.length = w.length) : (encodeCfg M w cfg).length = w.length := by
  simp only [encodeCfg, List.length_map,
    length_encodeCellsAux (by rw [hl] : w.length = cfg.tape.length)]

/-- The `i`-th cell of the encoding. -/
theorem getElem_encodeCfg {w : List Γ} {cfg : LBAConfig Q Γ} {i : ℕ}
    (hl : cfg.tape.length = w.length) (hhead : cfg.head < w.length)
    (hi : i < w.length) :
    (encodeCfg M w cfg)[i]'(by rw [length_encodeCfg hl]; exact hi) =
      cellSym (w[i]'hi) ((cfg.tape[i]?).join)
        (if i = cfg.head then some cfg.state else none) true
        (LBABoundary.ofHead i w.length) := by
  have hlen : w.length = cfg.tape.length := hl.symm
  have hget := getElem_encodeCellsAux (w := w) (tape := cfg.tape)
    (h := if cfg.head < w.length then some cfg.head else none) (q := cfg.state)
    (start := 0) (total := w.length) hlen hi
  rw [if_pos hhead] at hget
  have hgoal : (encodeCfg M w cfg)[i]'(by rw [length_encodeCfg hl]; exact hi) =
      cellTupleSym ((encodeCellsAux w cfg.tape
        (if cfg.head < w.length then some cfg.head else none) cfg.state 0 w.length)[i]'
        (by rw [length_encodeCellsAux hlen]; exact hi)) := by
    simp only [encodeCfg, List.getElem_map]
  rw [hgoal, if_pos hhead, hget]
  by_cases hihead : i = cfg.head
  · subst hihead
    simp only [cellTupleSym, if_pos rfl, Nat.zero_add]
  · have hne1 : (some cfg.head : Option ℕ) ≠ some i := by simp [Ne.symm hihead]
    have hne2 : i ≠ cfg.head := hihead
    simp only [cellTupleSym, if_neg hne1, if_neg hne2, Nat.zero_add]

/-- One step preserves the tape length. -/
theorem step_tape_length {c c' : LBAConfig Q Γ} (h : M.Step c c') :
    c'.tape.length = c.tape.length := by
  obtain ⟨q', b', mv, -, rfl, -⟩ := h
  simp [List.length_set]

/-- One step keeps the head on the tape, when the source head is on the tape. -/
theorem step_head_lt {c c' : LBAConfig Q Γ} (h : M.Step c c')
    (hhead : c.head < c.tape.length) : c'.head < c'.tape.length := by
  obtain ⟨q', b', mv, -, rfl, hlegal⟩ := h
  rw [List.length_set]
  cases mv <;> simp only [LBAMove.moveHead, LBAMove.legal] at hlegal ⊢ <;> omega

/-- Reachable configurations have the input tape length and the head on the
tape, for a nonempty input word. -/
theorem reachable_tape_length {w : List Γ} {c : LBAConfig Q Γ} (hw : w ≠ [])
    (h : Relation.ReflTransGen M.Step (M.initCfg w) c) :
    c.tape.length = w.length ∧ c.head < c.tape.length := by
  induction h with
  | refl =>
    constructor
    · simp [LinearBoundedAutomaton.initCfg]
    · cases w with
      | nil => contradiction
      | cons a w =>
        simp only [LinearBoundedAutomaton.initCfg]
        exact Nat.zero_lt_succ _
  | tail _ hstep ih =>
    obtain ⟨hl, hhead⟩ := ih
    refine ⟨(step_tape_length hstep).trans hl, ?_⟩
    exact step_head_lt hstep hhead

/-- One machine step is one grammar derivation step on encodings. -/
theorem derives_encodeCfg_step {w : List Γ} {c c' : LBAConfig Q Γ}
    (_hw : w ≠ []) (hstep : M.Step c c')
    (hl : c.tape.length = w.length) (hhead : c.head < c.tape.length) :
    Derives M.lbaGrammar (encodeCfg M w c) (encodeCfg M w c') := by
  obtain ⟨q', b', mv, hmem, rfl, hlegal⟩ := hstep
  have hbnd : LBABoundary.ofHead c.head c.tape.length =
      LBABoundary.ofHead c.head w.length := by rw [hl]
  rw [hbnd] at hmem
  have hlen : (encodeCfg M w ⟨q', c.tape.set c.head b', mv.moveHead c.head⟩).length =
      w.length := by
    apply length_encodeCfg
    rw [List.length_set]
    exact hl
  have hlen' : (encodeCfg M w c).length = w.length := length_encodeCfg hl
  have htape : (c.tape.set c.head b').length = c.tape.length := List.length_set
  have hlegal' : mv.moveHead c.head < w.length := by
    cases mv with
    | left =>
      show c.head - 1 < w.length
      omega
    | stay =>
      have hleg : c.head < c.tape.length := hlegal
      rw [← hl]; exact hleg
    | right =>
      have hleg : c.head + 1 < c.tape.length := hlegal
      rw [← hl]; exact hleg
  have hhead_w : c.head < w.length := by rw [← hl]; exact hhead
  have hheadm1_w : c.head - 1 < w.length := by rw [← hl]; omega
  cases mv with
  | stay =>
    have hgetNew : ∀ {i : ℕ} (hi : i < w.length),
        (encodeCfg M w ⟨q', c.tape.set c.head b', LBAMove.stay.moveHead c.head⟩)[i]'
          (by rw [length_encodeCfg (by rw [List.length_set]; exact hl)]; exact hi) =
          cellSym (w[i]'hi) (((c.tape.set c.head b')[i]?).join)
            (if i = LBAMove.stay.moveHead c.head then some q' else none) true
            (LBABoundary.ofHead i w.length) := by
      intro i hi
      exact getElem_encodeCfg
        (cfg := ⟨q', c.tape.set c.head b', LBAMove.stay.moveHead c.head⟩)
        (hl := by rw [List.length_set]; exact hl) (hhead := hlegal') (hi := hi)
    have hset : (encodeCfg M w ⟨q', c.tape.set c.head b',
        LBAMove.stay.moveHead c.head⟩) =
        (encodeCfg M w c).set c.head
          (cellSym (w[c.head]'hhead_w) b' (some q') true
            (LBABoundary.ofHead c.head w.length)) := by
      apply List.ext_getElem
      · rw [hlen, List.length_set, hlen']
      · intro i hi hi'
        have hi' : i < w.length := by rw [hlen] at hi; exact hi
        by_cases hieq : i = c.head
        · subst hieq
          rw [List.getElem_set_self]
          rw [hgetNew hi']
          have hget : (c.tape.set c.head b')[c.head]? = some b' :=
            List.getElem?_set_self hhead
          rw [hget]
          simp [LBAMove.moveHead, Option.join_some]
        · rw [List.getElem_set_of_ne (Ne.symm hieq)]
          rw [hgetNew hi']
          rw [getElem_encodeCfg hl hhead_w hi']
          have htape_i : ((c.tape.set c.head b')[i]?).join = (c.tape[i]?).join := by
            rw [List.getElem?_set]
            simp [Ne.symm hieq]
          rw [htape_i]
          simp [hieq, show i ≠ LBAMove.stay.moveHead c.head by simp [LBAMove.moveHead, hieq]]
    rw [hset]
    apply derives_set_single (hi := by rw [hlen']; exact hhead_w)
    rw [getElem_encodeCfg hl hhead_w (by rw [← hl]; exact hhead)]
    simp only [if_pos rfl]
    exact mem_rule_sim_stay (q := c.state) (q' := q') (read := (c.tape[c.head]?).join)
      (write := b') (orig := w[c.head]'hhead_w)
      (bnd := LBABoundary.ofHead c.head w.length) hmem
  | right =>
    have hhead1 : c.head + 1 < c.tape.length := hlegal
    have hhead1_w : c.head + 1 < w.length := by rw [← hl]; exact hlegal
    have hgetNew : ∀ {i : ℕ} (hi : i < w.length),
        (encodeCfg M w ⟨q', c.tape.set c.head b', LBAMove.right.moveHead c.head⟩)[i]'
          (by rw [length_encodeCfg (by rw [List.length_set]; exact hl)]; exact hi) =
          cellSym (w[i]'hi) (((c.tape.set c.head b')[i]?).join)
            (if i = LBAMove.right.moveHead c.head then some q' else none) true
            (LBABoundary.ofHead i w.length) := by
      intro i hi
      exact getElem_encodeCfg
        (cfg := ⟨q', c.tape.set c.head b', LBAMove.right.moveHead c.head⟩)
        (hl := by rw [List.length_set]; exact hl) (hhead := hlegal') (hi := hi)
    have hset : (encodeCfg M w ⟨q', c.tape.set c.head b',
        LBAMove.right.moveHead c.head⟩) =
        ((encodeCfg M w c).set c.head (cellSym (w[c.head]'hhead_w) b' none true
          (LBABoundary.ofHead c.head w.length))).set (c.head + 1)
          (cellSym (w[c.head + 1]'hhead1_w) ((c.tape[c.head + 1]?).join) (some q') true
            (LBABoundary.ofHead (c.head + 1) w.length)) := by
      apply List.ext_getElem
      · rw [hlen]
        simp [hlen', List.length_set]
      · intro i hi hi'
        have hi' : i < w.length := by
          rw [hlen] at hi
          exact hi
        by_cases hieq : i = c.head
        · subst hieq
          rw [List.getElem_set_of_ne (show c.head + 1 ≠ c.head by omega),
            List.getElem_set_self]
          rw [hgetNew hi']
          have hget : (c.tape.set c.head b')[c.head]? = some b' :=
            List.getElem?_set_self hhead
          rw [hget]
          simp [LBAMove.moveHead, Option.join_some, show c.head ≠ c.head + 1 by omega]
        · by_cases hieq1 : i = c.head + 1
          · subst hieq1
            rw [List.getElem_set_self]
            rw [hgetNew hi']
            have htape_i : ((c.tape.set c.head b')[c.head + 1]?).join =
                (c.tape[c.head + 1]?).join := by
              have hne : c.head + 1 ≠ c.head := by omega
              rw [List.getElem?_set]
              simp [hne]
            rw [htape_i]
            simp [hieq, show c.head + 1 = LBAMove.right.moveHead c.head by
              simp [LBAMove.moveHead]]
          · rw [List.getElem_set_of_ne (Ne.symm hieq1), List.getElem_set_of_ne (Ne.symm hieq)]
            rw [hgetNew hi']
            rw [getElem_encodeCfg hl hhead_w hi']
            have htape_i : ((c.tape.set c.head b')[i]?).join = (c.tape[i]?).join := by
              rw [List.getElem?_set]
              simp [Ne.symm hieq]
            rw [htape_i]
            simp [hieq, hieq1, show i ≠ LBAMove.right.moveHead c.head by
              simp [LBAMove.moveHead]; omega]
    rw [hset]
    apply derives_set_two (hi := by rw [hlen']; omega)
    rw [getElem_encodeCfg hl hhead_w (by rw [← hl]; exact hhead),
      getElem_encodeCfg hl hhead_w (by rw [← hl]; exact hhead1)]
    simp only [if_pos rfl, if_neg (show c.head + 1 ≠ c.head by omega)]
    exact mem_rule_sim_right (q := c.state) (q' := q')
      (read := (c.tape[c.head]?).join) (write := b') (orig := w[c.head]'hhead_w)
      (orig₂ := w[c.head + 1]'hhead1_w) (cur₂ := ((c.tape[c.head + 1]?).join))
      (bnd := LBABoundary.ofHead c.head w.length)
      (bnd₂ := LBABoundary.ofHead (c.head + 1) w.length) hmem
  | left =>
    obtain ⟨hpos, -⟩ := hlegal
    have hhead1 : c.head - 1 < c.tape.length := by omega
    have hgetNew : ∀ {i : ℕ} (hi : i < w.length),
        (encodeCfg M w ⟨q', c.tape.set c.head b', LBAMove.left.moveHead c.head⟩)[i]'
          (by rw [length_encodeCfg (by rw [List.length_set]; exact hl)]; exact hi) =
          cellSym (w[i]'hi) (((c.tape.set c.head b')[i]?).join)
            (if i = LBAMove.left.moveHead c.head then some q' else none) true
            (LBABoundary.ofHead i w.length) := by
      intro i hi
      exact getElem_encodeCfg
        (cfg := ⟨q', c.tape.set c.head b', LBAMove.left.moveHead c.head⟩)
        (hl := by rw [List.length_set]; exact hl) (hhead := hlegal') (hi := hi)
    have hset : (encodeCfg M w ⟨q', c.tape.set c.head b',
        LBAMove.left.moveHead c.head⟩) =
        ((encodeCfg M w c).set (c.head - 1)
          (cellSym (w[c.head - 1]'hheadm1_w) ((c.tape[c.head - 1]?).join) (some q') true
            (LBABoundary.ofHead (c.head - 1) w.length))).set c.head
          (cellSym (w[c.head]'hhead_w) b' none true
            (LBABoundary.ofHead c.head w.length)) := by
      apply List.ext_getElem
      · rw [hlen]
        simp [hlen', List.length_set]
      · intro i hi hi'
        have hi' : i < w.length := by
          rw [hlen] at hi
          exact hi
        by_cases hieq : i = c.head
        · subst hieq
          rw [List.getElem_set_self]
          rw [hgetNew hi']
          have hget : (c.tape.set c.head b')[c.head]? = some b' :=
            List.getElem?_set_self hhead
          rw [hget]
          simp [LBAMove.moveHead, Option.join_some, hpos, show c.head ≠ c.head - 1 by omega]
        · by_cases hieq1 : i = c.head - 1
          · subst hieq1
            rw [List.getElem_set_of_ne (by omega : c.head ≠ c.head - 1),
              List.getElem_set_self]
            rw [hgetNew hi']
            have htape_i : ((c.tape.set c.head b')[c.head - 1]?).join =
                (c.tape[c.head - 1]?).join := by
              have hne : c.head - 1 ≠ c.head := by omega
              rw [List.getElem?_set]
              simp [hne, Ne.symm hne]
            rw [htape_i]
            simp [show c.head - 1 = LBAMove.left.moveHead c.head by
              simp [LBAMove.moveHead, hpos]]
          · rw [List.getElem_set_of_ne (Ne.symm hieq),
              List.getElem_set_of_ne (Ne.symm hieq1)]
            rw [hgetNew hi']
            rw [getElem_encodeCfg hl hhead_w hi']
            have htape_i : ((c.tape.set c.head b')[i]?).join = (c.tape[i]?).join := by
              rw [List.getElem?_set]
              simp [Ne.symm hieq]
            rw [htape_i]
            simp [hieq, hieq1, show i ≠ LBAMove.left.moveHead c.head by
              simp [LBAMove.moveHead, hpos]; omega]
    rw [hset]
    apply derives_set_two' (i := c.head - 1) (j := c.head)
      (hi := by rw [hlen']; omega) (hj := by omega)
    rw [getElem_encodeCfg hl hhead_w (by rw [← hl]; exact hhead1),
      getElem_encodeCfg hl hhead_w (by rw [← hl]; exact hhead)]
    simp only [if_neg (show c.head - 1 ≠ c.head by omega), if_pos rfl]
    exact mem_rule_sim_left (q := c.state) (q' := q')
      (read := (c.tape[c.head]?).join) (write := b') (orig := w[c.head]'hhead_w)
      (orig₂ := w[c.head - 1]'hheadm1_w) (cur₂ := ((c.tape[c.head - 1]?).join))
      (bnd := LBABoundary.ofHead c.head w.length)
      (bnd₂ := LBABoundary.ofHead (c.head - 1) w.length) hmem

/-! ### Conversion and completeness -/

/-- Every cell of an encoding has head state `none` or the given state. -/
theorem encodeCellsAux_state {w : List Γ} {tape : List (Option Γ)} {h : Option ℕ} {q : Q}
    {start total : ℕ}
    {cell : Γ × Option Γ × Option Q × Bool × LBABoundary}
    (hmem : cell ∈ encodeCellsAux w tape h q start total) :
    cell.2.2.1 = none ∨ cell.2.2.1 = some q := by
  induction w generalizing tape h start with
  | nil => simp [encodeCellsAux] at hmem
  | cons a w ih =>
    cases tape with
    | nil => simp [encodeCellsAux] at hmem
    | cons cur tape =>
      cases h with
      | none =>
        simp only [encodeCellsAux, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact ih hmem
      | some n =>
        cases n with
        | zero =>
          simp only [encodeCellsAux, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inr rfl
          · exact ih hmem
        | succ n =>
          simp only [encodeCellsAux, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inl rfl
          · exact ih hmem

/-- Every cell of an encoding is active. -/
theorem encodeCellsAux_active {w : List Γ} {tape : List (Option Γ)} {h : Option ℕ} {q : Q}
    {start total : ℕ}
    {cell : Γ × Option Γ × Option Q × Bool × LBABoundary}
    (hmem : cell ∈ encodeCellsAux w tape h q start total) :
    cell.2.2.2.1 = true := by
  induction w generalizing tape h start with
  | nil => simp [encodeCellsAux] at hmem
  | cons a w ih =>
    cases tape with
    | nil => simp [encodeCellsAux] at hmem
    | cons cur tape =>
      cases h with
      | none =>
        simp only [encodeCellsAux, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rfl
        · exact ih hmem
      | some n =>
        cases n with
        | zero =>
          simp only [encodeCellsAux, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact ih hmem
        | succ n =>
          simp only [encodeCellsAux, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact ih hmem

/-- The original symbols of an encoding are the input word. -/
theorem map_orig_encodeCellsAux {w : List Γ} {tape : List (Option Γ)} {h : Option ℕ} {q : Q}
    {start total : ℕ} (hl : w.length = tape.length) :
    (encodeCellsAux w tape h q start total).map (fun cell ↦ termSym (Q := Q) cell.1) =
      w.map (termSym (Q := Q)) := by
  induction w generalizing tape h start with
  | nil => rfl
  | cons a w ih =>
    cases tape with
    | nil => simp at hl
    | cons cur tape =>
      simp only [List.length_cons] at hl
      have hl' : w.length = tape.length := Nat.succ.inj hl
      cases h with
      | none =>
        rw [show encodeCellsAux (a :: w) (cur :: tape) none q start total =
            (a, cur, none, true, LBABoundary.ofHead start total) ::
              encodeCellsAux w tape none q (start + 1) total from rfl,
          List.map_cons, List.map_cons, ih (tape := tape) hl' (h := none)]
      | some n =>
        cases n with
        | zero =>
          rw [show encodeCellsAux (a :: w) (cur :: tape) (some 0) q start total =
              (a, cur, some q, true, LBABoundary.ofHead start total) ::
                encodeCellsAux w tape none q (start + 1) total from rfl,
            List.map_cons, List.map_cons, ih (tape := tape) hl' (h := none)]
        | succ n =>
          rw [show encodeCellsAux (a :: w) (cur :: tape) (some (n + 1)) q start total =
              (a, cur, none, true, LBABoundary.ofHead start total) ::
                encodeCellsAux w tape (some n) q (start + 1) total from rfl,
            List.map_cons, List.map_cons, ih (tape := tape) hl' (h := some n)]

/-- A list of cells, each non-head or accepting, converts to its original
terminals. -/
theorem derives_convert_cells :
    ∀ (cells : List (Γ × Option Γ × Option Q × Bool × LBABoundary)),
    (∀ cell ∈ cells, (cell.2.2.1 = none ∨ cell.2.2.1 = some M.qAcc) ∧
      cell.2.2.2.1 = true) →
    Derives M.lbaGrammar (cells.map cellTupleSym)
      (cells.map fun cell ↦ termSym (Q := Q) cell.1) := by
  intro cells
  induction cells with
  | nil => intro _; exact Cslib.Decidability.Rewriting.Derives.refl _
  | cons cell cells ih =>
    intro hcell
    have hhead : (cell.2.2.1 = none ∨ cell.2.2.1 = some M.qAcc) ∧
        cell.2.2.2.1 = true :=
      hcell _ List.mem_cons_self
    have htail : ∀ cell' ∈ cells,
        (cell'.2.2.1 = none ∨ cell'.2.2.1 = some M.qAcc) ∧ cell'.2.2.2.1 = true :=
      fun cell' hmem ↦ hcell _ (List.mem_cons_of_mem _ hmem)
    obtain ⟨a, cur, st, active, bnd⟩ := cell
    obtain ⟨hst, hact⟩ := hhead
    simp only [List.map_cons]
    have hact' : active = true := hact
    subst hact'
    have hst' : st = none ∨ st = some M.qAcc := hst
    have hstep : Derives M.lbaGrammar
        [cellSym a cur st true bnd] [termSym a] := by
      rcases hst' with rfl | rfl
      · exact derives_singleton_cell (mem_rule_conv_none a cur bnd)
      · exact derives_singleton_cell (mem_rule_conv_acc a cur bnd)
    exact derives_append hstep (ih htail)

/-- Derivations along a run, keeping the tape length and head on the tape. -/
theorem derives_encodeCfg_reflTransGen {w : List Γ} {c : LBAConfig Q Γ} (hw : w ≠ [])
    (h : Relation.ReflTransGen M.Step (M.initCfg w) c) :
    c.tape.length = w.length ∧ c.head < c.tape.length ∧
      Derives M.lbaGrammar (encodeCfg M w (M.initCfg w)) (encodeCfg M w c) := by
  induction h with
  | refl =>
    refine ⟨by simp [LinearBoundedAutomaton.initCfg], ?_, ?_⟩
    · cases w with
      | nil => contradiction
      | cons a w => simp only [LinearBoundedAutomaton.initCfg]; exact Nat.zero_lt_succ _
    · exact Cslib.Decidability.Rewriting.Derives.refl _
  | tail _ hstep ih =>
    obtain ⟨hl, hhead, hder⟩ := ih
    refine ⟨(step_tape_length hstep).trans hl, ?_, ?_⟩
    · exact step_head_lt hstep hhead
    · exact derives_trans hder (derives_encodeCfg_step hw hstep hl hhead)

/-- **If the LBA accepts a nonempty word, the grammar derives it.** This is
one inclusion of the LBA-to-grammar direction. -/
theorem lba_accepts_implies_grammar_derives {w : List Γ} (hw : w ≠ [])
    (h : M.Accepts w) : w ∈ Cslib.Language.language M.lbaGrammar := by
  obtain ⟨c, hrun, hstate⟩ := h
  obtain ⟨hl, hhead, hder⟩ := derives_encodeCfg_reflTransGen hw hrun
  have hgen : Derives M.lbaGrammar [startSym (Γ := Γ) (Q := Q)]
      (encodeCfg M w (M.initCfg w)) :=
    derives_trans (derives_start_genEncode w hw) (derives_gen_activate w)
  have hconv : Derives M.lbaGrammar (encodeCfg M w c) (w.map (termSym (Q := Q))) := by
    have hcells : ∀ cell ∈ encodeCellsAux w c.tape
        (if c.head < w.length then some c.head else none) c.state 0 w.length,
        (cell.2.2.1 = none ∨ cell.2.2.1 = some M.qAcc) ∧ cell.2.2.2.1 = true := by
      intro cell hmem
      refine ⟨?_, encodeCellsAux_active hmem⟩
      rcases encodeCellsAux_state hmem with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hstate] at h; exact h)
    have hconv' := derives_convert_cells
      (encodeCellsAux w c.tape (if c.head < w.length then some c.head else none) c.state
        0 w.length)
      hcells
    rw [map_orig_encodeCellsAux (by rw [hl] : w.length = c.tape.length)] at hconv'
    exact hconv'
  have hfinal : Derives M.lbaGrammar [startSym (Γ := Γ) (Q := Q)]
      (w.map (termSym (Q := Q))) :=
    derives_trans hgen (derives_trans hder hconv)
  exact hfinal

end LinearBoundedAutomaton

end Language
end Cslib
