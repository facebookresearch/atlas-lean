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

/-- A sequential transducer: deterministic transitions emitting output words, plus
initial and final outputs. -/
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

/-- The run of a sequential transducer from `q` on `xs`: the final state and the
concatenated output word (excluding initial and final outputs). -/
def runFrom (S : SequentialTransducer State In Out) (q : State) : List In → State × List Out
  | [] => (q, [])
  | a :: xs =>
      let (q', w) := S.step q a
      let (q'', w') := S.runFrom q' xs
      (q'', w ++ w')

/-- The final state of the run from `q` on `xs`. -/
def runState (S : SequentialTransducer State In Out) (q : State) (xs : List In) : State :=
  (S.runFrom q xs).1

/-- The output word of the run from `q` on `xs`. -/
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

/-- The final state after reading `a :: xs` is the final state after reading `xs`
from the successor of `q` on `a`. -/
theorem runState_cons (S : SequentialTransducer State In Out) (q : State) (a : In)
    (xs : List In) :
    S.runState q (a :: xs) = S.runState (S.step q a).1 xs :=
  rfl

/-- The output on reading `a :: xs` is the output of the first step followed by the
output on `xs` from the successor state. -/
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

/-- Running on `xs ++ ys` is running on `xs` and then on `ys` from the reached state. -/
theorem runState_append (S : SequentialTransducer State In Out) (xs ys : List In)
    (q : State) :
    S.runState q (xs ++ ys) = S.runState (S.runState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, runState_cons, ih]

/-- The output on `xs ++ ys` is the output on `xs` followed by the output on `ys`
from the reached state. -/
theorem runOut_append (S : SequentialTransducer State In Out) (xs ys : List In)
    (q : State) :
    S.runOut q (xs ++ ys) =
      S.runOut q xs ++ S.runOut (S.runState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, runOut_cons, runState_cons, ih, List.append_assoc]

/-- `S` translates `xs` to `ys` when the run from the start state ends in an accepting
state and the initial, per-letter, and final outputs concatenate to `ys`. -/
def Translates (S : SequentialTransducer State In Out) (xs : List In)
    (ys : List Out) : Prop :=
  S.runState S.start xs ∈ S.accept ∧
    S.initOut ++ S.runOut S.start xs ++ S.finalOut (S.runState S.start xs) = ys

-- Note: there is no global instance of upstream's `Transducer` class for
-- `SequentialTransducer`: that class requires the input and output alphabets to live in the
-- same universe, while `SequentialTransducer` is universe-polymorphic. Use
-- `SequentialTransducer.Translates` directly.

/-- The composition of two sequential transducers: run the first, feed its output
(including the initial output, which is fed through the second transducer before any
input is read) through the second. -/
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

/-- The successor state of the composition on one letter. -/
theorem comp_step_fst (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (q₁ : State₁) (q₂ : State₂)
    (a : In) :
    ((comp S₁ S₂).step (q₁, q₂) a).1 =
      ((S₁.step q₁ a).1, S₂.runState q₂ (S₁.step q₁ a).2) :=
  rfl

/-- The output of the composition on one letter. -/
theorem comp_step_snd (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (q₁ : State₁) (q₂ : State₂)
    (a : In) :
    ((comp S₁ S₂).step (q₁, q₂) a).2 = S₂.runOut q₂ (S₁.step q₁ a).2 :=
  rfl

/-- The state reached by the composition is the pair of the states reached by the
two transducers, the second one fed the first one's output. -/
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

/-- The output of the composition is the second transducer's output on the first
transducer's output. -/
theorem comp_runOut (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) (q₁ : State₁)
    (q₂ : State₂) :
    (comp S₁ S₂).runOut (q₁, q₂) xs = S₂.runOut q₂ (S₁.runOut q₁ xs) := by
  induction xs generalizing q₁ q₂ with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runOut_cons, comp_step_fst, comp_step_snd, ih,
        SequentialTransducer.runOut_cons, SequentialTransducer.runOut_append]

/-- The second transducer's state after the first transducer's whole output
(including its initial and final outputs). -/
theorem comp_runState_initOut (S₁ : SequentialTransducer State₁ In Mid)
    (S₂ : SequentialTransducer State₂ Mid Out) (xs : List In) :
    S₂.runState S₂.start
        (S₁.initOut ++ S₁.runOut S₁.start xs ++
          S₁.finalOut (S₁.runState S₁.start xs)) =
      S₂.runState (S₂.runState (S₂.runState S₂.start S₁.initOut)
        (S₁.runOut S₁.start xs)) (S₁.finalOut (S₁.runState S₁.start xs)) := by
  rw [List.append_assoc, runState_append, runState_append]

/-- The second transducer's output on the first transducer's whole output. -/
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

/-- The total output of the composition, in terms of the second transducer's run on
the first transducer's whole output. -/
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

/-- **Composition of sequential transducers**: the composition translates `xs` to `ys`
exactly when some intermediate word `zs` is translated by the first transducer and
then by the second. -/
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

/-- The preimage of a language under a sequential transducer: the inputs whose
(output) translation lands in the language. -/
def preimage (S : SequentialTransducer State In Out) (L : Language Out) : Language In :=
  {xs | ∃ ys ∈ L, S.Translates xs ys}

/-- The product DFA of a sequential transducer `S` with a DFA `M` for the output
language: it feeds `S`'s output words through `M`, starting `M` in the state reached
on `S`'s initial output. -/
def preimageDFA (S : SequentialTransducer State In Out) (M : DFA Out σ) :
    DFA In (State × σ) where
  step := fun (q, r) a =>
    let (q', w) := S.step q a
    (q', M.evalFrom r w)
  start := (S.start, M.evalFrom M.start S.initOut)
  accept := {p : State × σ | p.1 ∈ S.accept ∧
    M.evalFrom p.2 (S.finalOut p.1) ∈ M.accept}

/-- Evaluation in the product DFA: the transducer state and the DFA state reached
on the output word. -/
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

/-- The product DFA accepts exactly the preimage. -/
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

/-- **Inverse sequential transduction preserves regular languages**: if `L` is regular,
then the set of inputs whose translation under `S` lands in `L` is regular. The proof
is the product of `S` with a DFA for `L`, started in the DFA state reached on `S`'s
initial output. -/
theorem isRegular_preimage [Finite State] (S : SequentialTransducer State In Out)
    {L : Language Out} (hL : L.IsRegular) : (S.preimage L).IsRegular := by
  let _ : Fintype State := Fintype.ofFinite State
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  let _ : Fintype σ := hσ
  exact Language.isRegular_iff.2
    ⟨State × σ, inferInstance, S.preimageDFA M, S.preimageDFA_accepts M⟩

end SequentialTransducer

/-- A Mealy machine: the output of a transition depends on the state and the input
letter. -/
structure MealyMachine (State In Out : Type*) where
  /-- The transition function: successor state and output letter. -/
  step : State → In → State × Out
  /-- The start state. -/
  start : State

namespace MealyMachine

/-- The run of a Mealy machine from `q` on `xs`: the final state and the output word. -/
def runFrom (M : MealyMachine State In Out) (q : State) :
    List In → State × List Out
  | [] => (q, [])
  | a :: xs =>
      let (q', o) := M.step q a
      let (q'', w) := M.runFrom q' xs
      (q'', o :: w)

/-- The final state of the run from `q` on `xs`. -/
def runState (M : MealyMachine State In Out) (q : State) (xs : List In) : State :=
  (M.runFrom q xs).1

/-- The output word of the run from `q` on `xs`. -/
def runOut (M : MealyMachine State In Out) (q : State) (xs : List In) : List Out :=
  (M.runFrom q xs).2

/-- The final state after reading `a :: xs`. -/
theorem runState_cons (M : MealyMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runState q (a :: xs) = M.runState (M.step q a).1 xs :=
  rfl

/-- The output on reading `a :: xs`. -/
theorem runOut_cons (M : MealyMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runOut q (a :: xs) = (M.step q a).2 :: M.runOut (M.step q a).1 xs :=
  rfl

/-- The transduction of a Mealy machine: the output word on `xs` from the start state. -/
def transduce (M : MealyMachine State In Out) (xs : List In) : List Out :=
  (M.runFrom M.start xs).2

/-- A Mealy machine as a sequential transducer: each transition emits its single
output letter, every state accepts, and the initial and final outputs are empty. -/
def toSequential (M : MealyMachine State In Out) : SequentialTransducer State In Out where
  step q a := let (q', o) := M.step q a; (q', [o])
  start := M.start
  accept := Set.univ
  initOut := []
  finalOut := fun _ => []

/-- The sequential rendering of a Mealy machine has the same final states as the
Mealy machine. -/
theorem seq_runState_eq (M : MealyMachine State In Out) (xs : List In) (q : State) :
    (M.toSequential).runState q xs = M.runState q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      rw [SequentialTransducer.runState_cons, MealyMachine.runState_cons]
      change (M.toSequential).runState (M.step q a).1 xs = M.runState (M.step q a).1 xs
      exact ih _

/-- The sequential rendering of a Mealy machine has the same output words as the
Mealy machine. -/
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

/-- A Mealy machine and its sequential rendering translate the same words. -/
theorem toSequential_accept (M : MealyMachine State In Out) :
    (M.toSequential).accept = Set.univ :=
  rfl

/-- The initial output of the sequential rendering of a Mealy machine is empty. -/
theorem toSequential_initOut (M : MealyMachine State In Out) :
    (M.toSequential).initOut = [] :=
  rfl

/-- The final outputs of the sequential rendering of a Mealy machine are empty. -/
theorem toSequential_finalOut (M : MealyMachine State In Out) (q : State) :
    (M.toSequential).finalOut q = [] :=
  rfl

/-- A Mealy machine and its sequential rendering translate the same words. -/
theorem translates_toSequential_iff (M : MealyMachine State In Out) (xs : List In)
    (ys : List Out) :
    (M.toSequential).Translates xs ys ↔ M.transduce xs = ys := by
  unfold SequentialTransducer.Translates
  rw [toSequential_accept, toSequential_initOut, toSequential_finalOut]
  simp only [Set.mem_univ, true_and, List.nil_append, List.append_nil]
  rw [seq_runOut_eq]
  rfl

end MealyMachine

/-- A Moore machine: the output depends only on the state. -/
structure MooreMachine (State In Out : Type*) where
  /-- The transition function: successor state on an input letter. -/
  step : State → In → State
  /-- The output of a state. -/
  out : State → Out
  /-- The start state. -/
  start : State

namespace MooreMachine

/-- The run of a Moore machine from `q` on `xs`: the final state and the output word,
which includes the output of the starting state. -/
def runFrom (M : MooreMachine State In Out) (q : State) :
    List In → State × List Out
  | [] => (q, [M.out q])
  | a :: xs =>
      let q' := M.step q a
      let (q'', w) := M.runFrom q' xs
      (q'', M.out q :: w)

/-- The final state of the run from `q` on `xs`. -/
def runState (M : MooreMachine State In Out) (q : State) (xs : List In) : State :=
  (M.runFrom q xs).1

/-- The output word of the run from `q` on `xs`. -/
def runOut (M : MooreMachine State In Out) (q : State) (xs : List In) : List Out :=
  (M.runFrom q xs).2

/-- The final state after reading `a :: xs`. -/
theorem runState_cons (M : MooreMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runState q (a :: xs) = M.runState (M.step q a) xs :=
  rfl

/-- The output on reading `a :: xs`. -/
theorem runOut_cons (M : MooreMachine State In Out) (q : State) (a : In)
    (xs : List In) :
    M.runOut q (a :: xs) = M.out q :: M.runOut (M.step q a) xs :=
  rfl

/-- The transduction of a Moore machine: the output word on `xs` from the start state. -/
def transduce (M : MooreMachine State In Out) (xs : List In) : List Out :=
  (M.runFrom M.start xs).2

/-- A Moore machine as a sequential transducer: each transition emits the output of
its target state, the initial output is the output of the start state, every state
accepts, and the final outputs are empty. -/
def toSequential (M : MooreMachine State In Out) : SequentialTransducer State In Out where
  step q a := (M.step q a, [M.out (M.step q a)])
  start := M.start
  accept := Set.univ
  initOut := [M.out M.start]
  finalOut := fun _ => []

/-- The output of a Moore machine from `q` is the output of `q` followed by the
output of its sequential rendering. -/
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

/-- A Moore machine and its sequential rendering translate the same words. -/
theorem toSequential_accept (M : MooreMachine State In Out) :
    (M.toSequential).accept = Set.univ :=
  rfl

/-- The initial output of the sequential rendering of a Moore machine is the output
of the start state. -/
theorem toSequential_initOut (M : MooreMachine State In Out) :
    (M.toSequential).initOut = [M.out M.start] :=
  rfl

/-- The final outputs of the sequential rendering of a Moore machine are empty. -/
theorem toSequential_finalOut (M : MooreMachine State In Out) (q : State) :
    (M.toSequential).finalOut q = [] :=
  rfl

/-- A Moore machine and its sequential rendering translate the same words. -/
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
