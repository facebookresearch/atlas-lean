/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sequential transducers, Mealy machines, and Moore machines
-/
module

public import Cslib.Computability.Automata.Transducers.Transducer
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Computability.Language

/-!
# Sequential transducers, Mealy machines, and Moore machines

A sequential transducer (`SequentialTransducer`) is a deterministic finite-state
transducer: in each state, reading an input letter moves to a successor state and
emits a (possibly empty) output word. An initial output word is emitted before any
input is read, and a final output word is emitted on acceptance, depending on the
final state. A word `xs` is translated to `ys` (`SequentialTransducer.Translates`)
when the run from the start state ends in an accepting state and the concatenation
of the initial, per-letter, and final outputs is `ys`.

Mealy machines (output on transitions) and Moore machines (output on states) are the
two classical special cases, both rendered as sequential transducers
(`MealyMachine.toSequential`, `MooreMachine.toSequential`) with the expected
transduction.

## Main results

* `SequentialTransducer.translates_comp_iff`: composition of sequential transducers
  (`SequentialTransducer.comp`, a product construction) translates `xs` to `ys`
  exactly when some intermediate word `zs` is translated by the first and then by
  the second transducer.
* `SequentialTransducer.isRegular_preimage`: inverse sequential transduction preserves
  regular languages: the set of inputs whose output lands in a regular language is
  regular (a product of the transducer with a DFA for the language).
* The forward image under a sequential transducer is also regular; it needs an
  ε-NFA expanding each transition's output word, and is stated as a `theorem_wanted`
  in `WantedExt/TheoryOfComputation/SequentialTransducerImageWanted.lean`.
-/

@[expose] public section

namespace Cslib.Automata

variable {State State₁ State₂ In Mid Out σ : Type*}

/-- **Sequential transducer.** A sequential transducer with states in a type $Q$, input letters in
a type $\Sigma$ and output letters in a type $\Gamma$ consists of a transition function assigning
to each state $q \in Q$ and input letter $a \in \Sigma$ a successor state in $Q$ and an output
word over $\Gamma$, a start state in $Q$, a set of accepting states $F \subseteq Q$, an initial
output word over $\Gamma$, and, for each state in $Q$, a final output word over $\Gamma$.

No finiteness is assumed of $Q$, $\Sigma$ or $\Gamma$. -/
structure SequentialTransducer (State In Out : Type*) where
  /-- On input letter `a` in state `q`, the successor state and the emitted output word. -/
  step : State → In → State × List Out
  /-- The start state. -/
  start : State
  /-- The set of accepting states. -/
  accept : Set State
  /-- The output word emitted before any input is read. -/
  initOut : List Out
  /-- The output word emitted on acceptance, depending on the final state. -/
  finalOut : State → List Out

namespace SequentialTransducer

/-- **Run of a sequential transducer.** The run of a sequential transducer $S$ from a state $q$
on an input word $a_1 \cdots a_n$ is the pair $(q_n, w_1 w_2 \cdots w_n)$, where $q_0 = q$ and,
for each $1 \le i \le n$, $S$ moves from $q_{i-1}$ on $a_i$ to $q_i$ emitting the word $w_i$.
The initial output and the final outputs of $S$ are not included. -/
def runFrom (S : SequentialTransducer State In Out) (q : State) : List In → State × List Out
  | [] => (q, [])
  | a :: xs =>
      let (q', w) := S.step q a
      let (q'', w') := S.runFrom q' xs
      (q'', w ++ w')

/-- **Final state of a sequential transducer run.** For a sequential transducer $S$, a state $q$
and an input word $w$, the final state of the run of $S$ from $q$ on $w$ is obtained by starting
in $q$, reading the letters of $w$ in order, moving at each letter to the successor state given
by the transition function of $S$, and taking the state reached at the end. -/
def runState (S : SequentialTransducer State In Out) (q : State) (xs : List In) : State :=
  (S.runFrom q xs).1

/-- **Output word of a sequential transducer run.** For a sequential transducer $S$, a state $q$
and an input word $x$, the output word of the run from $q$ on $x$ is the concatenation of the
output words that $S$ emits on the successive letters of $x$, starting in $q$ and moving to the
successor state after each letter; the initial and final outputs are not included. -/
def runOut (S : SequentialTransducer State In Out) (q : State) (xs : List In) : List Out :=
  (S.runFrom q xs).2

theorem runFrom_nil (S : SequentialTransducer State In Out) (q : State) :
    S.runFrom q [] = (q, []) :=
  rfl

theorem runFrom_cons (S : SequentialTransducer State In Out) (q : State) (a : In)
    (xs : List In) :
    S.runFrom q (a :: xs) =
      let (q', w) := S.step q a
      let (q'', w') := S.runFrom q' xs
      (q'', w ++ w') :=
  rfl

/-- **Final state of a sequential transducer run on a nonempty word.** Let $S$ be a sequential
transducer, $q$ a state, $a$ an input letter and $w$ an input word, and let $q'$ be the successor
state of $q$ on $a$ under the transition function of $S$. Then the final state of the run of $S$
from $q$ on the word $aw$ equals the final state of the run of $S$ from $q'$ on $w$. -/
theorem runState_cons (S : SequentialTransducer State In Out) (q : State) (a : In)
    (xs : List In) :
    S.runState q (a :: xs) = S.runState (S.step q a).1 xs :=
  rfl

/-- **Output of a sequential transducer on a nonempty word.** Let $S$ be a sequential
transducer, $q$ a state, $a$ an input letter and $x$ an input word, and let $q'$ and $w$ be the
successor state and the output word of $S$ in state $q$ on letter $a$. The output word of the
run of $S$ from $q$ on $ax$ is $w$ followed by the output word of the run from $q'$ on $x$. -/
theorem runOut_cons (S : SequentialTransducer State In Out) (q : State) (a : In)
    (xs : List In) :
    S.runOut q (a :: xs) = (S.step q a).2 ++ S.runOut (S.step q a).1 xs :=
  rfl

theorem runState_nil (S : SequentialTransducer State In Out) (q : State) :
    S.runState q [] = q :=
  rfl

theorem runOut_nil (S : SequentialTransducer State In Out) (q : State) :
    S.runOut q [] = [] :=
  rfl

/-- **Final state of a sequential transducer on a concatenation.** For a sequential transducer
$S$, a state $q$ and input words $x$ and $y$, the final state of the run of $S$ from $q$ on $xy$
is the final state of the run on $y$ from the final state of the run from $q$ on $x$. -/
theorem runState_append (S : SequentialTransducer State In Out) (xs ys : List In)
    (q : State) :
    S.runState q (xs ++ ys) = S.runState (S.runState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, runState_cons, ih]

/-- **Output of a sequential transducer on a concatenation.** For a sequential transducer $S$,
a state $q$ and input words $x$ and $y$, the output word of the run of $S$ from $q$ on $xy$ is
the output word of the run from $q$ on $x$ followed by the output word of the run on $y$ from
the final state of the run from $q$ on $x$. -/
theorem runOut_append (S : SequentialTransducer State In Out) (xs ys : List In)
    (q : State) :
    S.runOut q (xs ++ ys) =
      S.runOut q xs ++ S.runOut (S.runState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, runOut_cons, runState_cons, ih, List.append_assoc]

/-- **Translation by a sequential transducer.** A sequential transducer $S$ translates an input
word $x$ to an output word $y$ when the run of $S$ on $x$ from its start state ends in an
accepting state $q$ and $y$ is the concatenation of the initial output of $S$, the output words
emitted by the transitions along the run, and the final output of $S$ at $q$. -/
def Translates (S : SequentialTransducer State In Out) (xs : List In)
    (ys : List Out) : Prop :=
  S.runState S.start xs ∈ S.accept ∧
    S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs) = ys

-- Note: there is no global instance of upstream's `Transducer` class for
-- `SequentialTransducer`: that class requires the input and output alphabets to live in the
-- same universe, while `SequentialTransducer` is universe-polymorphic. Use
-- `SequentialTransducer.Translates` directly.

/-- **Composition of sequential transducers.** Let $S_1$ be a sequential transducer from $I$ to
$M$ with start state $s_1$, initial output $\iota_1$ and final output map $\phi_1$, and let $S_2$
be one from $M$ to $O$ with start state $s_2$, initial output $\iota_2$ and final output map
$\phi_2$. For a transducer $S$, a state $q$ and a word $w$, write $\delta_S(q, w)$ for the state
$S$ reaches by reading $w$ from $q$ and $\lambda_S(q, w)$ for the concatenation of the words it
emits along the way. The composition of $S_1$ and $S_2$ is the sequential transducer from $I$ to
$O$ whose states are the pairs $(q_1, q_2)$ of a state of $S_1$ and a state of $S_2$, where:
reading a letter $a$ in state $(q_1, q_2)$, if $S_1$ reading $a$ in $q_1$ moves to $q_1'$ and
emits $w$, the composition moves to $(q_1', \delta_{S_2}(q_2, w))$ and emits
$\lambda_{S_2}(q_2, w)$; the start state is $(s_1, \delta_{S_2}(s_2, \iota_1))$; the initial
output is $\iota_2$ followed by $\lambda_{S_2}(s_2, \iota_1)$; a state $(q_1, q_2)$ is accepting
when $q_1$ is accepting for $S_1$ and $\delta_{S_2}(q_2, \phi_1(q_1))$ is accepting for $S_2$; and
the final output at $(q_1, q_2)$ is $\lambda_{S_2}(q_2, \phi_1(q_1))$ followed by
$\phi_2(\delta_{S_2}(q_2, \phi_1(q_1)))$.

In words: run $S_1$ and feed its output, including its initial output (fed through $S_2$ before
any input is read) and its final output, through $S_2$. -/
def comp (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) :
    SequentialTransducer (State₁ × State₂) In Out where
  step := fun (q₁, q₂) a =>
    let (q₁', w₁) := S₁.step q₁ a
    let (q₂', w₂) := S₂.runFrom q₂ w₁
    ((q₁', q₂'), w₂)
  start := (S₁.start, S₂.runState S₂.start S₁.initOut)
  accept := {p : State₁ × State₂ | p.1 ∈ S₁.accept ∧
    S₂.runState p.2 (S₁.finalOut p.1) ∈ S₂.accept}
  initOut := S₂.initOut ++ S₂.runOut S₂.start S₁.initOut
  finalOut := fun (q₁, q₂) =>
    S₂.runOut q₂ (S₁.finalOut q₁) ++ S₂.finalOut (S₂.runState q₂ (S₁.finalOut q₁))

/-- **One step of a composite transducer: the successor state.** Let $S_1$ be a sequential
transducer from $I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. Let $q_1$ be a
state of $S_1$, $q_2$ a state of $S_2$ and $a \in I$ a letter, and suppose that $S_1$, reading
$a$ in state $q_1$, moves to $q_1'$ and emits the word $w$. Then $C$, reading $a$ in state
$(q_1, q_2)$, moves to $(q_1', q_2')$, where $q_2'$ is the state $S_2$ reaches by reading $w$
from $q_2$. -/
theorem comp_step_fst (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (q₁ : State₁) (q₂ : State₂)
    (a : In) :
    ((comp S₁ S₂).step (q₁, q₂) a).1 =
      ((S₁.step q₁ a).1, S₂.runState q₂ (S₁.step q₁ a).2) :=
  rfl

/-- **One step of a composite transducer: the output.** Let $S_1$ be a sequential transducer from
$I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. Let $q_1$ be a state of $S_1$,
$q_2$ a state of $S_2$ and $a \in I$ a letter, and let $w$ be the word $S_1$ emits when it reads
$a$ in state $q_1$. Then the word $C$ emits when it reads $a$ in state $(q_1, q_2)$ is the
concatenation of the words $S_2$ emits while reading $w$ from $q_2$. -/
theorem comp_step_snd (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (q₁ : State₁) (q₂ : State₂)
    (a : In) :
    ((comp S₁ S₂).step (q₁, q₂) a).2 = S₂.runOut q₂ (S₁.step q₁ a).2 :=
  rfl

/-- **States reached by a composite sequential transducer.** Let $S_1$ be a sequential transducer
from $I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. For a transducer $S$, a
state $q$ and a word $w$, write $\delta_S(q, w)$ for the state $S$ reaches by reading $w$ from
$q$ and $\lambda_S(q, w)$ for the concatenation of the words it emits along the way (without
initial or final output). Then for all states $q_1$ of $S_1$ and $q_2$ of $S_2$ and every word
$x$ over $I$,
$\delta_C((q_1, q_2), x) = (\delta_{S_1}(q_1, x), \delta_{S_2}(q_2, \lambda_{S_1}(q_1, x)))$. -/
theorem comp_runState (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) (q₁ : State₁)
    (q₂ : State₂) :
    (comp S₁ S₂).runState (q₁, q₂) xs =
      (S₁.runState q₁ xs, S₂.runState q₂ (S₁.runOut q₁ xs)) := by
  induction xs generalizing q₁ q₂ with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runState_cons, comp_step_fst, ih,
        SequentialTransducer.runState_cons, SequentialTransducer.runOut_cons,
        SequentialTransducer.runState_append]

/-- **Output of a composite sequential transducer.** Let $S_1$ be a sequential transducer from
$I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. For a transducer $S$, a state
$q$ and a word $w$, write $\lambda_S(q, w)$ for the concatenation of the words $S$ emits while
reading $w$ from $q$ (without initial or final output). Then for all states $q_1$ of $S_1$ and
$q_2$ of $S_2$ and every word $x$ over $I$,
$\lambda_C((q_1, q_2), x) = \lambda_{S_2}(q_2, \lambda_{S_1}(q_1, x))$. -/
theorem comp_runOut (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) (q₁ : State₁)
    (q₂ : State₂) :
    (comp S₁ S₂).runOut (q₁, q₂) xs = S₂.runOut q₂ (S₁.runOut q₁ xs) := by
  induction xs generalizing q₁ q₂ with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runOut_cons, comp_step_fst, comp_step_snd, ih,
        SequentialTransducer.runOut_cons, SequentialTransducer.runOut_append]

/-- **State of the second transducer after the first one's whole output.** Let $S_1$ be a
sequential transducer from $I$ to $M$ and $S_2$ one from $M$ to $O$, with start states $s_1$ and
$s_2$. For a transducer $S$, a state $q$ and a word $w$, write $\delta_S(q, w)$ for the state $S$
reaches by reading $w$ from $q$ and $\lambda_S(q, w)$ for the concatenation of the words it emits
along the way (without initial or final output); juxtaposition of words is concatenation. For a
word $x$ over $I$, let $\iota$ be the initial output of $S_1$, let $u = \lambda_{S_1}(s_1, x)$,
and let $f$ be the final output of $S_1$ at $\delta_{S_1}(s_1, x)$. Then
$\delta_{S_2}(s_2, \iota u f) = \delta_{S_2}(\delta_{S_2}(\delta_{S_2}(s_2, \iota), u), f)$. -/
theorem comp_runState_initOut (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) :
    S₂.runState S₂.start
        (S₁.initOut ++ S₁.runOut S₁.start xs ++
          S₁.finalOut (S₁.runState S₁.start xs)) =
      S₂.runState (S₂.runState (S₂.runState S₂.start S₁.initOut)
        (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)) := by
  rw [List.append_assoc, runState_append, runState_append]

/-- **Output of the second transducer on the first one's whole output.** Let $S_1$ be a
sequential transducer from $I$ to $M$ and $S_2$ one from $M$ to $O$, with start states $s_1$ and
$s_2$. For a transducer $S$, a state $q$ and a word $w$, write $\delta_S(q, w)$ for the state $S$
reaches by reading $w$ from $q$ and $\lambda_S(q, w)$ for the concatenation of the words it emits
along the way (without initial or final output); juxtaposition of words is concatenation. For a
word $x$ over $I$, let $\iota$ be the initial output of $S_1$, let $u = \lambda_{S_1}(s_1, x)$,
let $f$ be the final output of $S_1$ at $\delta_{S_1}(s_1, x)$, and let
$r = \delta_{S_2}(s_2, \iota)$. Then
$\lambda_{S_2}(s_2, \iota u f) = \lambda_{S_2}(s_2, \iota) \, \lambda_{S_2}(r, u) \,
\lambda_{S_2}(\delta_{S_2}(r, u), f)$. -/
theorem comp_runOut_initOut (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) :
    S₂.runOut S₂.start
        (S₁.initOut ++ S₁.runOut S₁.start xs ++
          S₁.finalOut (S₁.runState S₁.start xs)) =
      S₂.runOut S₂.start S₁.initOut ++
        S₂.runOut (S₂.runState S₂.start S₁.initOut) (S₁.runOut S₁.start xs) ++
          S₂.runOut (S₂.runState (S₂.runState S₂.start S₁.initOut)
            (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)) := by
  rw [List.append_assoc, runOut_append, runOut_append, ← List.append_assoc]

/-- **Total output of a composite sequential transducer.** Let $S_1$ be a sequential transducer
from $I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. For a sequential
transducer $S$ with start state $s$, initial output $\iota$ and final output map $\phi$, and a
word $x$, let $\delta_S(s, x)$ be the state $S$ reaches by reading $x$ from $s$ and
$\lambda_S(s, x)$ the concatenation of the words it emits along the way, and call the
concatenation $\iota \, \lambda_S(s, x) \, \phi(\delta_S(s, x))$ the whole output of $S$ on $x$
(acceptance plays no role). Then for every word $x$ over $I$, the whole output of $C$ on $x$
equals the whole output of $S_2$ on the whole output of $S_1$ on $x$. -/
theorem comp_output_eq (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) :
    (comp S₁ S₂).initOut ++ (comp S₁ S₂).runOut (comp S₁ S₂).start xs ++
        (comp S₁ S₂).finalOut ((comp S₁ S₂).runState (comp S₁ S₂).start xs) =
      S₂.initOut ++ S₂.runOut S₂.start
        (S₁.initOut ++ S₁.runOut S₁.start xs ++
          S₁.finalOut (S₁.runState S₁.start xs)) ++
        S₂.finalOut (S₂.runState S₂.start
          (S₁.initOut ++ S₁.runOut S₁.start xs ++
            S₁.finalOut (S₁.runState S₁.start xs))) := by
  rw [comp_runState, comp_runOut]
  show (S₂.initOut ++ S₂.runOut S₂.start S₁.initOut) ++
      S₂.runOut (S₂.runState S₂.start S₁.initOut) (S₁.runOut S₁.start xs) ++
        (S₂.runOut (S₂.runState (S₂.runState S₂.start S₁.initOut)
            (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)) ++
          S₂.finalOut (S₂.runState (S₂.runState (S₂.runState S₂.start S₁.initOut)
            (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)))) = _
  rw [comp_runState_initOut, comp_runOut_initOut]
  simp only [List.append_assoc]

/-- **Translations of a composite sequential transducer.** Let $S_1$ be a sequential transducer
from an alphabet $A$ to an alphabet $B$, and $S_2$ one from $B$ to an alphabet $C$. For every word
$x$ over $A$ and every word $y$ over $C$, the composition of $S_1$ and $S_2$ translates $x$ to $y$
if and only if there is a word $z$ over $B$ such that $S_1$ translates $x$ to $z$ and $S_2$
translates $z$ to $y$. -/
theorem translates_comp_iff (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) (ys : List Out) :
    (comp S₁ S₂).Translates xs ys ↔
      ∃ zs, S₁.Translates xs zs ∧ S₂.Translates zs ys := by
  constructor
  · intro h
    obtain ⟨hacc, hout⟩ := h
    rw [comp_runState] at hacc
    have hacc' : S₁.runState S₁.start xs ∈ S₁.accept ∧
        S₂.runState (S₂.runState (S₂.runState S₂.start S₁.initOut)
          (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)) ∈
          S₂.accept := hacc
    obtain ⟨hacc₁, hacc₂⟩ := hacc'
    refine ⟨S₁.initOut ++ S₁.runOut S₁.start xs ++ S₁.finalOut (S₁.runState S₁.start xs),
      ⟨hacc₁, rfl⟩, ?_, ?_⟩
    · rw [comp_runState_initOut]
      exact hacc₂
    · exact (comp_output_eq S₁ S₂ xs).symm.trans hout
  · rintro ⟨zs, ⟨hacc₁, hz₁⟩, hacc₂, hout₂⟩
    have hz : zs = S₁.initOut ++ S₁.runOut S₁.start xs ++
        S₁.finalOut (S₁.runState S₁.start xs) :=
      hz₁.symm
    subst hz
    rw [comp_runState_initOut] at hacc₂
    constructor
    · rw [comp_runState]
      show S₁.runState S₁.start xs ∈ S₁.accept ∧ _
      exact ⟨hacc₁, hacc₂⟩
    · exact (comp_output_eq S₁ S₂ xs).trans hout₂

/-- **Preimage of a language under a sequential transducer.** Let $S$ be a sequential transducer
with input alphabet $\Sigma$ and output alphabet $\Gamma$, and let $L$ be a language over
$\Gamma$. The preimage of $L$ under $S$ is the language over $\Sigma$ consisting of the words $x$
for which there is a word $y \in L$ such that $S$ translates $x$ to $y$. -/
def preimage (S : SequentialTransducer State In Out) (L : Language Out) : Language In :=
  {xs | ∃ ys ∈ L, S.Translates xs ys}

/-- **Product DFA of a sequential transducer and a DFA.** Let $S$ be a sequential transducer
with state type $Q$, input alphabet $\Sigma$ and output alphabet $\Gamma$, and let $M$ be a DFA
over $\Gamma$ with state type $P$. The product DFA of $S$ and $M$ is the DFA over $\Sigma$ with
state type $Q \times P$ defined as follows. In state $(q, r)$ on a letter $a$, if $S$ moves from
$q$ to $q'$ emitting the word $w$, it moves to $(q', r')$, where $r'$ is the state $M$ reaches
from $r$ on $w$. Its start state is $(q_0, r_0)$, where $q_0$ is the start state of $S$ and
$r_0$ is the state $M$ reaches from its start state on the initial output of $S$. A state
$(q, r)$ is accepting when $q$ is an accepting state of $S$ and the state $M$ reaches from $r$
on the final output of $S$ at $q$ is an accepting state of $M$. -/
def preimageDFA (S : SequentialTransducer State In Out) (M : DFA Out σ) :
    DFA In (State × σ) where
  step := fun (q, r) a =>
    let (q', w) := S.step q a
    (q', M.evalFrom r w)
  start := (S.start, M.evalFrom M.start S.initOut)
  accept := {p : State × σ | p.1 ∈ S.accept ∧
    M.evalFrom p.2 (S.finalOut p.1) ∈ M.accept}

/-- **Runs of the product DFA.** Let $S$ be a sequential transducer and $M$ a DFA over the
output alphabet of $S$. For every input word $x$, state $q$ of $S$ and state $r$ of $M$, the
product DFA of $S$ and $M$, started in $(q, r)$ and run on $x$, ends in the state $(q', r')$,
where $q'$ is the final state of the run of $S$ from $q$ on $x$ and $r'$ is the state that $M$
reaches from $r$ on the output word of that run. -/
theorem preimageDFA_evalFrom (S : SequentialTransducer State In Out) (M : DFA Out σ)
    (xs : List In) (q : State) (r : σ) :
    (S.preimageDFA M).evalFrom (q, r) xs =
      (S.runState q xs, M.evalFrom r (S.runOut q xs)) := by
  induction xs generalizing q r with
  | nil => rfl
  | cons a xs ih =>
      rw [DFA.evalFrom_cons]
      change (S.preimageDFA M).evalFrom ((S.step q a).1, M.evalFrom r (S.step q a).2) xs =
        _
      rw [ih, runState_cons, runOut_cons, ← DFA.evalFrom_of_append]

/-- **The product DFA recognizes the preimage.** Let $S$ be a sequential transducer with output
alphabet $\Gamma$ and let $M$ be a DFA over $\Gamma$. The language accepted by the product DFA
of $S$ and $M$ equals the preimage under $S$ of the language accepted by $M$, that is, the set
of input words that $S$ translates to some word accepted by $M$. -/
theorem preimageDFA_accepts (S : SequentialTransducer State In Out) (M : DFA Out σ) :
    (S.preimageDFA M).accepts = S.preimage (M.accepts) := by
  apply Language.ext
  intro xs
  constructor
  · intro h
    rw [DFA.mem_accepts] at h
    change (S.preimageDFA M).evalFrom (S.start, M.evalFrom M.start S.initOut) xs ∈
      (S.preimageDFA M).accept at h
    rw [preimageDFA_evalFrom] at h
    change S.runState S.start xs ∈ S.accept ∧
      M.evalFrom (M.evalFrom (M.evalFrom M.start S.initOut) (S.runOut S.start xs))
        (S.finalOut (S.runState S.start xs)) ∈ M.accept at h
    obtain ⟨hacc, hmem⟩ := h
    show ∃ ys ∈ M.accepts, S.Translates xs ys
    refine ⟨S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs),
      ?_, ⟨hacc, rfl⟩⟩
    show M.evalFrom M.start
        (S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs)) ∈
        M.accept
    have h1 : M.evalFrom M.start
        (S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs)) =
          M.evalFrom (M.evalFrom (M.evalFrom M.start S.initOut) (S.runOut S.start xs))
            (S.finalOut (S.runState S.start xs)) := by
      rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
    rw [h1]
    exact hmem
  · rintro ⟨ys, hys, hacc, hout⟩
    show xs ∈ (S.preimageDFA M).accepts
    rw [DFA.mem_accepts]
    change (S.preimageDFA M).evalFrom (S.start, M.evalFrom M.start S.initOut) xs ∈
      (S.preimageDFA M).accept
    rw [preimageDFA_evalFrom]
    change S.runState S.start xs ∈ S.accept ∧
      M.evalFrom (M.evalFrom (M.evalFrom M.start S.initOut) (S.runOut S.start xs))
        (S.finalOut (S.runState S.start xs)) ∈ M.accept
    refine ⟨hacc, ?_⟩
    have h1 : M.evalFrom M.start
        (S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs)) =
          M.evalFrom (M.evalFrom (M.evalFrom M.start S.initOut) (S.runOut S.start xs))
            (S.finalOut (S.runState S.start xs)) := by
      rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
    rw [← h1, hout]
    exact (DFA.mem_accepts M).mp hys

/-- **Inverse sequential transduction preserves regular languages.** Let $S$ be a sequential
transducer with finitely many states, input alphabet $I$ and output alphabet $O$, and let $L$ be
a regular language over $O$. Then the preimage of $L$ under $S$, the set of words over $I$ that
$S$ translates to some word of $L$, is regular.

The proof is the product of $S$ with a DFA for $L$, started in the DFA state reached on the
initial output of $S$. -/
theorem isRegular_preimage [Finite State] (S : SequentialTransducer State In Out)
    {L : Language Out} (hL : L.IsRegular) : (S.preimage L).IsRegular := by
  let _ : Fintype State := Fintype.ofFinite State
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  let _ : Fintype σ := hσ
  exact Language.isRegular_iff.2
    ⟨State × σ, inferInstance, S.preimageDFA M, S.preimageDFA_accepts M⟩

end SequentialTransducer

/-- **Mealy machine.** A Mealy machine with state set $Q$, input alphabet $I$ and output
alphabet $O$ consists of a start state in $Q$ and a transition function that, given a state
$q \in Q$ and an input letter $a \in I$, returns a successor state in $Q$ and a single output
letter in $O$; thus the output of a transition depends on the state and the input letter. -/
structure MealyMachine (State In Out : Type*) where
  /-- The transition function: successor state and output letter. -/
  step : State → In → State × Out
  /-- The start state. -/
  start : State

namespace MealyMachine

/-- **Run of a Mealy machine.** The run of a Mealy machine $M$ from a state $q$ on an input
word $a_1 \cdots a_n$ is the pair $(q_n, o_1 \cdots o_n)$, where $q_0 = q$ and, for each
$1 \le i \le n$, $M$ moves from $q_{i-1}$ on $a_i$ to $q_i$ emitting the output letter $o_i$. -/
def runFrom (M : MealyMachine State In Out) (q : State) :
    List In → State × List Out
  | [] => (q, [])
  | a :: xs =>
      let (q', o) := M.step q a
      let (q'', w) := M.runFrom q' xs
      (q'', o :: w)

/-- **Final state of a Mealy machine run.** For a Mealy machine $M$, a state $q$ and an input
word $x$, the final state of the run from $q$ on $x$ is the state reached by starting in $q$
and moving, on each successive letter of $x$, to the successor state given by the transition
function of $M$; on the empty word it is $q$. -/
def runState (M : MealyMachine State In Out) (q : State) (xs : List In) : State :=
  (M.runFrom q xs).1

/-- **Output word of a Mealy machine run.** For a Mealy machine $M$, a state $q$ and an input
word $x$, the output word of $M$ from $q$ on $x$ is the second component of the run of $M$ from
$q$ on $x$: the word of output letters emitted along that run, one per input letter. -/
def runOut (M : MealyMachine State In Out) (q : State) (xs : List In) : List Out :=
  (M.runFrom q xs).2

/-- **Final state of a Mealy machine on a nonempty word.** Let $M$ be a Mealy machine, $q$ a
state, $a$ an input letter and $x$ an input word, and let $q'$ be the successor state of $M$ in
state $q$ on letter $a$. The final state of the run of $M$ from $q$ on $ax$ is the final state of
the run from $q'$ on $x$. -/
theorem runState_cons (M : MealyMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runState q (a :: xs) = M.runState (M.step q a).1 xs :=
  rfl

/-- **Output of a Mealy machine on a nonempty word.** Let $M$ be a Mealy machine, $q$ a state,
$a$ an input letter and $x$ an input word, and let $q'$ and $o$ be the successor state and the
output letter of $M$ in state $q$ on letter $a$. The output word of the run of $M$ from $q$ on
$ax$ is $o$ followed by the output word of the run from $q'$ on $x$. -/
theorem runOut_cons (M : MealyMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runOut q (a :: xs) = (M.step q a).2 :: M.runOut (M.step q a).1 xs :=
  rfl

/-- **Transduction of a Mealy machine.** Let $M$ be a Mealy machine with start state $q_0$. On
an input word $a_1 a_2 \cdots a_n$, for each $i$ let $q_i$ and $b_i$ be the state that $M$ moves
to and the letter that it outputs when it reads $a_i$ in state $q_{i-1}$. The transduction of
$M$ on this word is the output word $b_1 b_2 \cdots b_n$. -/
def transduce (M : MealyMachine State In Out) (xs : List In) : List Out :=
  (M.runFrom M.start xs).2

/-- **Mealy machine as a sequential transducer.** The sequential transducer of a Mealy machine
$M$ has the states and the start state of $M$; on an input letter $a$ in a state $q$ it moves
to the state that $M$ moves to and emits the one-letter word consisting of the letter that $M$
outputs on this transition. Every state accepts, and the initial and final outputs are empty. -/
def toSequential (M : MealyMachine State In Out) : SequentialTransducer State In Out where
  step q a := let (q', o) := M.step q a; (q', [o])
  start := M.start
  accept := Set.univ
  initOut := []
  finalOut := fun _ => []

/-- **The sequential transducer of a Mealy machine has the same final states.** For a Mealy
machine $M$, a state $q$ and an input word $w$, the final state of the run from $q$ on $w$ of the
sequential transducer associated with $M$ equals the final state of the run of $M$ from $q$ on
$w$. -/
theorem seq_runState_eq (M : MealyMachine State In Out) (xs : List In) (q : State) :
    (M.toSequential).runState q xs = M.runState q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runState_cons, MealyMachine.runState_cons]
      change (M.toSequential).runState (M.step q a).1 xs = M.runState (M.step q a).1 xs
      exact ih _

/-- **The sequential transducer of a Mealy machine has the same run outputs.** For a Mealy
machine $M$, a state $q$ and an input word $w$, the output word of the run from $q$ on $w$ of the
sequential transducer associated with $M$ (excluding its initial and final outputs) equals the
output word of the run of $M$ from $q$ on $w$. -/
theorem seq_runOut_eq (M : MealyMachine State In Out) (xs : List In) (q : State) :
    (M.toSequential).runOut q xs = M.runOut q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runOut_cons, MealyMachine.runOut_cons]
      change [(M.step q a).2] ++ (M.toSequential).runOut (M.step q a).1 xs =
        (M.step q a).2 :: M.runOut (M.step q a).1 xs
      rw [ih]
      rfl

/-- **Every state of the sequential transducer of a Mealy machine is accepting.** For a Mealy
machine $M$, the set of accepting states of the sequential transducer associated with $M$ is the
set of all states. -/
theorem toSequential_accept (M : MealyMachine State In Out) :
    (M.toSequential).accept = Set.univ :=
  rfl

/-- **Initial output of the sequential transducer of a Mealy machine.** For every Mealy machine
$M$, the initial output of the sequential transducer of $M$ is the empty word. -/
theorem toSequential_initOut (M : MealyMachine State In Out) :
    (M.toSequential).initOut = [] :=
  rfl

/-- **Final outputs of the sequential transducer of a Mealy machine.** For every Mealy machine
$M$ and every state $q$, the final output of the sequential transducer of $M$ at $q$ is the
empty word. -/
theorem toSequential_finalOut (M : MealyMachine State In Out) (q : State) :
    (M.toSequential).finalOut q = [] :=
  rfl

/-- **The sequential transducer of a Mealy machine computes its transduction.** For every Mealy
machine $M$, input word $x$ and output word $y$, the sequential transducer of $M$ translates $x$
to $y$ if and only if the transduction of $M$ on $x$ is $y$. -/
theorem translates_toSequential_iff (M : MealyMachine State In Out) (xs : List In)
    (ys : List Out) :
    (M.toSequential).Translates xs ys ↔ M.transduce xs = ys := by
  unfold SequentialTransducer.Translates
  rw [toSequential_accept, toSequential_initOut, toSequential_finalOut]
  simp only [Set.mem_univ, true_and, List.nil_append, List.append_nil]
  rw [seq_runOut_eq]
  rfl

end MealyMachine

/-- **Moore machine.** A Moore machine with state type $Q$, input alphabet $\Sigma$ and output
alphabet $\Gamma$ consists of a transition function, assigning to each state $q$ and input
letter $a$ a successor state $\delta(q, a) \in Q$, an output function $\lambda : Q \to \Gamma$,
and a start state $q_0 \in Q$. The output depends only on the state. -/
structure MooreMachine (State In Out : Type*) where
  /-- The transition function: successor state on an input letter. -/
  step : State → In → State
  /-- The output of a state. -/
  out : State → Out
  /-- The start state. -/
  start : State

namespace MooreMachine

/-- **Run of a Moore machine.** The run of a Moore machine $M$ with output function $\lambda$
from a state $q$ on an input word $a_1 \cdots a_n$ is the pair
$(q_n, \lambda(q_0) \lambda(q_1) \cdots \lambda(q_n))$, where $q_0 = q$ and, for each
$1 \le i \le n$, $q_i$ is the successor of $q_{i-1}$ on $a_i$. The output word has $n + 1$
letters and begins with the output of the starting state. -/
def runFrom (M : MooreMachine State In Out) (q : State) :
    List In → State × List Out
  | [] => (q, [M.out q])
  | a :: xs =>
      let q' := M.step q a
      let (q'', w) := M.runFrom q' xs
      (q'', M.out q :: w)

/-- **Final state of a Moore machine run.** For a Moore machine $M$, a state $q$ and an input
word $x$, the final state of the run from $q$ on $x$ is the state reached by starting in $q$
and moving, on each successive letter of $x$, to the successor state given by the transition
function of $M$; on the empty word it is $q$. -/
def runState (M : MooreMachine State In Out) (q : State) (xs : List In) : State :=
  (M.runFrom q xs).1

/-- **Output word of a Moore machine run.** For a Moore machine $M$, a state $q$ and an input
word $x$, the output word of $M$ from $q$ on $x$ is the second component of the run of $M$ from
$q$ on $x$: the outputs of the states visited along that run, starting with the output of $q$;
it has one more letter than $x$. -/
def runOut (M : MooreMachine State In Out) (q : State) (xs : List In) : List Out :=
  (M.runFrom q xs).2

/-- **Final state of a Moore machine run on a nonempty word.** For a Moore machine $M$ with
transition function $\delta$, a state $q$, an input letter $a$ and an input word $w$, the final
state of the run of $M$ from $q$ on the word $aw$ equals the final state of the run of $M$ from
$\delta(q, a)$ on $w$. -/
theorem runState_cons (M : MooreMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runState q (a :: xs) = M.runState (M.step q a) xs :=
  rfl

/-- **Output of a Moore machine on a nonempty word.** Let $M$ be a Moore machine, $q$ a state,
$a$ an input letter and $x$ an input word, and let $q'$ be the successor state of $M$ in state
$q$ on letter $a$. The output word of the run of $M$ from $q$ on $ax$ is the output of $q$
followed by the output word of the run from $q'$ on $x$. -/
theorem runOut_cons (M : MooreMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runOut q (a :: xs) = M.out q :: M.runOut (M.step q a) xs :=
  rfl

/-- **Transduction of a Moore machine.** Let $M$ be a Moore machine with start state $q_0$, and
write $o(q)$ for the output of a state $q$. On an input word $a_1 a_2 \cdots a_n$, let $q_i$ be
the state that $M$ moves to from $q_{i-1}$ on $a_i$. The transduction of $M$ on this word is the
output word $o(q_0)\, o(q_1) \cdots o(q_n)$, of length $n + 1$. -/
def transduce (M : MooreMachine State In Out) (xs : List In) : List Out :=
  (M.runFrom M.start xs).2

/-- **The sequential transducer of a Moore machine.** Let $M$ be a Moore machine with transition
function $\delta$, output function $\lambda$ and start state $q_0$. Its sequential transducer has
the same states and the start state $q_0$; reading a letter $a$ in state $q$ it moves to
$\delta(q, a)$ and emits the one-letter word $\lambda(\delta(q, a))$; every state is accepting;
the initial output is the one-letter word $\lambda(q_0)$; and every final output is empty. -/
def toSequential (M : MooreMachine State In Out) : SequentialTransducer State In Out where
  step q a := (M.step q a, [M.out (M.step q a)])
  start := M.start
  accept := Set.univ
  initOut := [M.out M.start]
  finalOut := fun _ => []

/-- **Moore machine output via its sequential rendering.** For a Moore machine $M$, a state $q$
and an input word $x$, the output word of the run of $M$ from $q$ on $x$ is the output of $q$
followed by the output word of the run of the sequential rendering of $M$ from $q$ on $x$. -/
theorem runOut_eq_cons (M : MooreMachine State In Out) (xs : List In) (q : State) :
    M.runOut q xs = M.out q :: (M.toSequential).runOut q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      rw [MooreMachine.runOut_cons, SequentialTransducer.runOut_cons]
      change M.out q :: M.runOut (M.step q a) xs =
        M.out q :: ([M.out (M.step q a)] ++ (M.toSequential).runOut (M.step q a) xs)
      rw [ih]
      rfl

/-- **Every state of the sequential transducer of a Moore machine is accepting.** For a Moore
machine $M$, the set of accepting states of the sequential transducer associated with $M$ is the
set of all states. -/
theorem toSequential_accept (M : MooreMachine State In Out) :
    (M.toSequential).accept = Set.univ :=
  rfl

/-- **Initial output of the sequential transducer of a Moore machine.** For every Moore machine
$M$, the initial output of the sequential transducer of $M$ is the one-letter word consisting of
the output of the start state of $M$. -/
theorem toSequential_initOut (M : MooreMachine State In Out) :
    (M.toSequential).initOut = [M.out M.start] :=
  rfl

/-- **Final outputs of the sequential transducer of a Moore machine.** For a Moore machine $M$
and every state $q$, the final output word at $q$ of the sequential transducer associated with
$M$ is empty. -/
theorem toSequential_finalOut (M : MooreMachine State In Out) (q : State) :
    (M.toSequential).finalOut q = [] :=
  rfl

/-- **The sequential transducer of a Moore machine computes its transduction.** For every Moore
machine $M$, input word $x$ and output word $y$, the sequential transducer of $M$ translates $x$
to $y$ if and only if the transduction of $M$ on $x$ is $y$. -/
theorem translates_toSequential_iff (M : MooreMachine State In Out) (xs : List In)
    (ys : List Out) :
    (M.toSequential).Translates xs ys ↔ M.transduce xs = ys := by
  unfold SequentialTransducer.Translates
  rw [toSequential_accept, toSequential_initOut, toSequential_finalOut]
  simp only [Set.mem_univ, true_and, List.append_nil]
  rw [show M.transduce xs = M.out M.start :: (M.toSequential).runOut M.start xs from by
    change M.runOut M.start xs = _
    exact runOut_eq_cons M xs M.start]
  simp only [List.cons_append, List.nil_append]
  rfl

end MooreMachine

end Cslib.Automata
