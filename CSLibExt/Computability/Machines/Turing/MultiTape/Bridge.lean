/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.CodeCompleteness
public import CSLibExt.Computability.Decidability.Basic
public import MathlibExt.Computability.RE
public import Mathlib.Computability.RE

/-!
# Multi-tape machines decide and recognize exactly the recursive predicates

CSLib's multi-tape machines (`Turing.MultiTapeTM`) and Mathlib's multi-stack machines
(`Turing.FinTM2`) decide and recognize the same predicates, through Mathlib's
`ComputablePred` and `REPred`. The direction proved here is multi-tape to recursion
theory: a multi-tape machine is simulated, up to a state relabelling, by the machine
of a code (`Code.exists_code_isRelabelling`, in
`Cslib.Turing.MultiTapeTM`), and the code's clocked evaluator is
primitive recursive (`Code.primrec_evalSteps`), so a multi-tape decider gives a
recursive decider for the same predicate (via Post's theorem, from its r.e. and
co-r.e. descriptions) and a multi-tape recognizer gives an r.e. description.
The converse direction, recursion theory to multi-tape machines, is not proved
here: it needs a multi-tape machine simulating a `FinTM2` (or a partial recursive
function), which is a separate construction. It is stated as a wanted theorem in
`WantedExt/TheoryOfComputation/MultiTapeBridge.lean` (deciders) and
`WantedExt/TheoryOfComputation/MultiTapeRecognizableBridge.lean` (recognizers).

The time/space form of the bridge is also wanted, not proved: the language-level
bridge here erases the time/space bounds, so it says nothing about polynomial
blowups. The wanted form is that a language is in multi-tape `Classes.P` iff
its characteristic function is in the canonical
`MetaMathlibExt.ComplexityTheory.P` (BACKLOG MT5), in
`WantedExt/TheoryOfComputation/MultiTapeComplexityBridge.lean`.

## Main definitions

- `Cslib.Decidability.MultiTapeDecidable`, `Cslib.Decidability.MultiTapeRecognizable`,
  `Cslib.Decidability.MultiTapeCoRecognizable`: decidable, recognizable and
  co-recognizable predicates on multi-tape machines, with the input convention of
  the single-tape and multi-stack classes: an element `a` is given to the machine
  as the binary word `encodeNat (encode a)`.

## Main results

- `Cslib.Decidability.MultiTapeRecognizable.rePred`,
  `Cslib.Decidability.MultiTapeDecidable.computablePred`: the multi-tape classes
  lie inside Mathlib's `REPred` and `ComputablePred`.
- `Cslib.Decidability.multiTapeDecidable_implies_tm2Decidable`,
  `Cslib.Decidability.multiTapeRecognizable_implies_tm2Recognizable`: multi-tape
  machines decide and recognize no more than multi-stack machines.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Corollary 3.15 (multi-tape machines decide the same languages as single-tape
  machines; here through recursion theory, not a direct simulation), Theorem 4.22
  (Post's theorem).
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory,
  Languages, and Computation*, 3rd ed., Pearson, 2007, §8.4 (multi-tape machines
  and the equivalence of machine models).
-/

@[expose] public section

set_option autoImplicit false

open Computability Encodable MetaMathlibExt.TM2Recursive
open Cslib.Turing Cslib.Turing.MultiTapeTM _root_.Turing

namespace Cslib.Decidability

variable {α : Type*} [Primcodable α] {p : α → Prop}

/-- **Decidability by multi-tape machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is decidable by a multi-tape machine when there are a number $k$ and a
deterministic Turing machine $M$ with finitely many states, a read-only input tape, $k$ work tapes
and a write-only output tape, all over the Boolean alphabet, such that for every $a \in \alpha$
there is a Boolean $b$ for which $M$ computes the one-letter word $b$ on the binary word of
$\mathrm{encode}(a)$ (least significant bit first), and $b$ is true exactly when $p(a)$ holds.
Here $M$ computes a word $v$ on an input word $w$ when its run started on $w$ halts with $v$ on
its output tape. -/
def MultiTapeDecidable (p : α → Prop) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ∀ a, ∃ b : Bool, tm.Computes (encodeNat (encode a)) [b] ∧ (b = true ↔ p a)

/-- **Recognizability by multi-tape machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is recognizable by a multi-tape machine when there are a number $k$ and
a deterministic Turing machine $M$ with finitely many states, a read-only input tape, $k$ work
tapes and a write-only output tape, all over the Boolean alphabet, such that for every
$a \in \alpha$, the run of $M$ started on the binary word of $\mathrm{encode}(a)$ (least
significant bit first) halts if and only if $p(a)$ holds. -/
def MultiTapeRecognizable (p : α → Prop) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ∀ a, (∃ o, tm.Computes (encodeNat (encode a)) o) ↔ p a

/-- **Co-recognizability by multi-tape machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is co-recognizable by a multi-tape machine when its complement
$\neg p$ is recognizable by a multi-tape machine. -/
def MultiTapeCoRecognizable (p : α → Prop) : Prop :=
  MultiTapeRecognizable fun a ↦ ¬p a

/-! ### Multi-tape machines are recursive -/

/-- The clocked evaluator of a code, as a primitive recursive function of the
input element and the clock. -/
private theorem computable_evalSteps_of_code {k : ℕ} (c : Cslib.Turing.MultiTapeTM.Code k) :
    Computable fun p : α × ℕ ↦ c.evalSteps (encodeNat (encode p.1)) p.2 := by
  have h1 : Computable fun q : Cslib.Turing.MultiTapeTM.Code k × List Bool × ℕ ↦
      q.1.evalSteps q.2.1 q.2.2 :=
    Cslib.Turing.MultiTapeTM.Code.primrec_evalSteps.to_comp
  have hmap : Computable fun p : α × ℕ ↦ (c, encodeNat (encode p.1), p.2) :=
    (Computable.const c).pair
      (((primrec_encodeNat.to_comp.comp Computable.encode).comp Computable.fst).pair
        Computable.snd)
  have hcomp : Computable ((fun q : Cslib.Turing.MultiTapeTM.Code k × List Bool × ℕ ↦
      q.1.evalSteps q.2.1 q.2.2) ∘ fun p : α × ℕ ↦ (c, encodeNat (encode p.1), p.2)) :=
    h1.comp hmap
  exact hcomp.of_eq fun p ↦ rfl

/-- The evaluator returning a prescribed output, as a decidable test, is computable.
The proof composes the evaluator with the primitive recursive equality test
(`Primrec.eq.decide`); composition is stated in unreduced form and then reduced
by `of_eq`, so elaboration never has to unfold the evaluator to check that the
composition is the stated function. -/
private theorem computable_decide_evalSteps_eq {k : ℕ}
    (c : Cslib.Turing.MultiTapeTM.Code k) (o : List Bool) :
    Computable fun p : α × ℕ ↦
      decide (c.evalSteps (encodeNat (encode p.1)) p.2 = some o) :=
  Primrec.eq.decide.to_comp.comp (computable_evalSteps_of_code c)
    (Computable.const (some o))

/-- A predicate on `(input, clock)` given by the evaluator returning a prescribed
output is computable. -/
private theorem computablePred_evalSteps_eq {k : ℕ} (c : Cslib.Turing.MultiTapeTM.Code k)
    (o : List Bool) :
    ComputablePred fun p : α × ℕ ↦ c.evalSteps (encodeNat (encode p.1)) p.2 = some o :=
  Computable.computablePred (computable_decide_evalSteps_eq c o)

/-- A predicate on `(input, clock)` given by the evaluator being defined is computable. -/
private theorem computablePred_evalSteps_isSome {k : ℕ} (c : Cslib.Turing.MultiTapeTM.Code k) :
    ComputablePred fun p : α × ℕ ↦ (c.evalSteps (encodeNat (encode p.1)) p.2).isSome := by
  refine ComputablePred.computable_iff.mpr
    ⟨fun p : α × ℕ ↦ (c.evalSteps (encodeNat (encode p.1)) p.2).isSome, ?_, ?_⟩
  · have hsome : Computable ((fun q : Option (List Bool) ↦ q.isSome) ∘
        fun p : α × ℕ ↦ c.evalSteps (encodeNat (encode p.1)) p.2) :=
      Primrec.option_isSome.to_comp.comp (computable_evalSteps_of_code c)
    exact hsome.of_eq fun p ↦ rfl
  · funext p
    simp

/-- **A predicate recognizable by a multi-tape machine is recursively enumerable.** Let $\alpha$
be a primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding
is primitive recursive). If a predicate $p$ on $\alpha$ is recognizable by a multi-tape machine,
then $p$ is recursively enumerable, that is, the partial function on $\alpha$ that is defined,
with a trivial value, exactly where $p$ holds is partial recursive. -/
theorem MultiTapeRecognizable.rePred (h : MultiTapeRecognizable p) : REPred p := by
  obtain ⟨k, State, _, tm, hp⟩ := h
  obtain ⟨c, _e, _he, hrel⟩ := Cslib.Turing.MultiTapeTM.Code.exists_code_isRelabelling tm
  have key : ∀ a, p a ↔ ∃ T, (c.evalSteps (encodeNat (encode a)) T).isSome := by
    intro a
    rw [← hp a]
    constructor
    · rintro ⟨o, ho⟩
      obtain ⟨T, hT⟩ := (Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mp
        ((IsRelabelling.computes_iff hrel).mpr ho)
      exact ⟨T, by rw [hT]; rfl⟩
    · rintro ⟨T, hT⟩
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hT
      exact ⟨o, (IsRelabelling.computes_iff hrel).mp
        ((Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mpr ⟨T, ho⟩)⟩
  exact (MetaMathlibExt.REPred.exists
    (R := fun a T ↦ (c.evalSteps (encodeNat (encode a)) T).isSome)
    (computablePred_evalSteps_isSome c).to_re).of_eq fun a ↦ (key a).symm

/-- **A predicate decided by a multi-tape machine is recursively enumerable.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-tape machine, then
$p$ is recursively enumerable, that is, the partial function on $\alpha$ that is defined, with a
trivial value, exactly where $p$ holds is partial recursive. -/
theorem MultiTapeDecidable.rePred (h : MultiTapeDecidable p) : REPred p := by
  obtain ⟨k, State, _, tm, hp⟩ := h
  obtain ⟨c, _e, _he, hrel⟩ := Cslib.Turing.MultiTapeTM.Code.exists_code_isRelabelling tm
  have key : ∀ a, p a ↔
      ∃ T, c.evalSteps (encodeNat (encode a)) T = some [true] := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, hb, hbp⟩ := hp a
      have hbtrue : b = true := hbp.mpr ha
      obtain ⟨T, hT⟩ := (Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mp
        ((IsRelabelling.computes_iff hrel).mpr hb)
      exact ⟨T, hbtrue ▸ hT⟩
    · rintro ⟨T, hT⟩
      obtain ⟨b, hb, hbp⟩ := hp a
      have hcomp : tm.Computes (encodeNat (encode a)) [true] :=
        (IsRelabelling.computes_iff hrel).mp
          ((Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mpr ⟨T, hT⟩)
      have hbeq : [b] = [true] := computes_unique hb hcomp
      have hbtrue : b = true := (List.cons.inj hbeq).1
      exact hbp.mp hbtrue
  exact (MetaMathlibExt.REPred.exists
    (R := fun a T ↦ c.evalSteps (encodeNat (encode a)) T = some [true])
    (computablePred_evalSteps_eq c [true]).to_re).of_eq fun a ↦ (key a).symm

/-- **A predicate decided by a multi-tape machine has a recursively enumerable complement.** Let
$\alpha$ be a primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose
decoding is primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-tape
machine, then its complement $\neg p$ is recursively enumerable, that is, the partial function on
$\alpha$ that is defined, with a trivial value, exactly where $\neg p$ holds is partial
recursive. -/
theorem MultiTapeDecidable.rePred_not (h : MultiTapeDecidable p) :
    REPred fun a ↦ ¬p a := by
  obtain ⟨k, State, _, tm, hp⟩ := h
  obtain ⟨c, _e, _he, hrel⟩ := Cslib.Turing.MultiTapeTM.Code.exists_code_isRelabelling tm
  have key : ∀ a, ¬p a ↔
      ∃ T, c.evalSteps (encodeNat (encode a)) T = some [false] := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, hb, hbp⟩ := hp a
      have hbfalse : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hbp.mp rfl) ha
      obtain ⟨T, hT⟩ := (Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mp
        ((IsRelabelling.computes_iff hrel).mpr hb)
      exact ⟨T, hbfalse ▸ hT⟩
    · rintro ⟨T, hT⟩
      obtain ⟨b, hb, hbp⟩ := hp a
      have hcomp : tm.Computes (encodeNat (encode a)) [false] :=
        (IsRelabelling.computes_iff hrel).mp
          ((Cslib.Turing.MultiTapeTM.Code.computes_iff_exists_evalSteps c _ _).mpr ⟨T, hT⟩)
      have hbeq : [b] = [false] := computes_unique hb hcomp
      have hbfalse : b = false := (List.cons.inj hbeq).1
      intro ha
      have hbtrue : b = true := hbp.mpr ha
      rw [hbfalse] at hbtrue
      exact Bool.false_ne_true hbtrue
  exact (MetaMathlibExt.REPred.exists
    (R := fun a T ↦ c.evalSteps (encodeNat (encode a)) T = some [false])
    (computablePred_evalSteps_eq c [false]).to_re).of_eq fun a ↦ (key a).symm

/-- **A predicate decided by a multi-tape machine is computable.** Let $\alpha$ be a primcodable
type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive
recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-tape machine, then $p$ is
computable, that is, $p$ is decidable and its Boolean characteristic function
$\alpha \to \mathrm{Bool}$ is computable.

This is Post's theorem applied to $p$ and its complement, both recursively enumerable. -/
theorem MultiTapeDecidable.computablePred (h : MultiTapeDecidable p) : ComputablePred p :=
  ComputablePred.computable_iff_re_compl_re'.mpr ⟨h.rePred, h.rePred_not⟩

/-- **Multi-tape machines decide no more than multi-stack machines.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). Every predicate on $\alpha$ that is decidable by a multi-tape machine is
decidable by a multi-stack machine. -/
theorem multiTapeDecidable_implies_tm2Decidable (h : MultiTapeDecidable p) :
    TM2Decidable p :=
  tm2Decidable_iff_computablePred.mpr h.computablePred

/-- **Multi-tape machines recognize no more than multi-stack machines.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). Every predicate on $\alpha$ that is recognizable by a multi-tape machine is
recognizable by a multi-stack machine. -/
theorem multiTapeRecognizable_implies_tm2Recognizable (h : MultiTapeRecognizable p) :
    TM2Recognizable p :=
  tm2Recognizable_iff_rePred.mpr h.rePred

end Cslib.Decidability
