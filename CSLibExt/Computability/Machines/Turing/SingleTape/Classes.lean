/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Cslib.Foundations.Relation.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.Primrec.Basic

/-!
# Decidable and recognizable predicates on single-tape Turing machines

CSLib's single-tape machines (`Cslib.Turing.SingleTapeTM`) compute functions
`List Symbol → List Symbol`: a run starts at `initCfg l` and, to output `l'`, halts at
`haltCfg l'`, whose tape holds exactly `l'` (every other cell blank) with the head on its first
symbol (`SingleTapeTM.Outputs`). This file adds halting and the language classes of
computability theory on that model, with the input convention of the multi-stack classes
`Cslib.Decidability.TM2Decidable` and `Cslib.Decidability.TM2Recognizable`: an element `a` of a
`Primcodable` type is given to the machine as the binary word `encodeNat (encode a)`, written in
the machine's alphabet through an injective `ι : Bool → Symbol` (the input alphabet `{0, 1}`
inside the tape alphabet).

* `SingleTapeTM.HaltsOn tm l`: the run of `tm` on `l` reaches the halting state;
  `SingleTapeTM.HaltsFrom tm c`: the run from the configuration `c` does.
* `SingleTapeTM.Outputs.unique`: a machine outputs at most one word on each input.
* `SingleTapeDecidable p`: a machine outputs the one-symbol word `[ι b]` on the input of every
  `a`, with `b = true` exactly when `p a`.
* `SingleTapeRecognizable p`: a machine halts on the input of `a` exactly when `p a`.
* `SingleTapeCoRecognizable p`: the complement of `p` is recognizable.

Sipser defines these classes by accepting and rejecting states; a CSLib machine has a single
halting state, so here acceptance is halting (recognizers) or the output word (deciders), the
convention of CSLib's multi-tape `DecidableInTimeAndSpace`. Machines are only run on the code
words `encodeNat (encode a)`; for `Primcodable` types this is the usual notion, and it is the
convention of the multi-stack classes. The alphabet is part of the witness: a decider may use any
finite tape alphabet containing the two input bits. Injectivity of `ι` is what makes the decider's
answer meaningful: since outputs are unique (`Outputs.unique`), `[ι true]` and `[ι false]` are
different answers, while with `ι true = ι false` every predicate would have a trivial decider.

## Main definitions

- `Cslib.Turing.SingleTapeTM.HaltsOn`, `Cslib.Turing.SingleTapeTM.HaltsFrom`.
- `Cslib.Decidability.SingleTapeDecidable`, `Cslib.Decidability.SingleTapeRecognizable`,
  `Cslib.Decidability.SingleTapeCoRecognizable`.

## Main results

- `Cslib.Turing.SingleTapeTM.Outputs.haltsOn`, `Cslib.Turing.SingleTapeTM.Outputs.unique`,
  `Cslib.Turing.SingleTapeTM.rightUnique_transitionRelation`.
- `Cslib.Turing.SingleTapeTM.haltsOn_iff_haltsFrom`,
  `Cslib.Turing.SingleTapeTM.haltsFrom_iff_normalizable`: halting is halting from the initial
  configuration, and normalizability of the transition relation.
- `Cslib.Turing.SingleTapeTM.haltsFrom_iff_of_reflTransGen`,
  `Cslib.Turing.SingleTapeTM.haltsFrom_iff_of_step_eq`: halting from a configuration is invariant
  along a run.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Definitions 3.5 and 3.6, and co-Turing-recognizable languages in §4.2 (before Theorem 4.22).
-/

@[expose] public section

set_option autoImplicit false

open Relation

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- **Halting on an input.** A single-tape Turing machine $M$ halts on an input word $w$ when its
run from the initial configuration on $w$ (the start state, with $w$ written from the head
position rightwards on an otherwise blank tape) reaches, in finitely many steps (possibly none), a
configuration in the halting state. -/
def HaltsOn (tm : SingleTapeTM Symbol) (l : List Symbol) : Prop :=
  ∃ c : tm.Cfg, ReflTransGen tm.TransitionRelation (tm.initCfg l) c ∧ c.state = none

/-- **Halting from a configuration.** A single-tape Turing machine $M$ halts from a configuration
$c$ when its run from $c$ reaches, in finitely many steps (possibly none), a configuration in the
halting state.

Equivalently, $c$ is normalizable for the transition relation of $M$, since the configurations in
the halting state are exactly those without a successor; the same holds for CSLib's register
machines. -/
def HaltsFrom (tm : SingleTapeTM Symbol) (c : tm.Cfg) : Prop :=
  ∃ c' : tm.Cfg, ReflTransGen tm.TransitionRelation c c' ∧ c'.state = none

/-- **Halting on an input is halting from the initial configuration.** A single-tape Turing machine
$M$ halts on an input word $w$ if and only if $M$ halts from the initial configuration on $w$. -/
theorem haltsOn_iff_haltsFrom {tm : SingleTapeTM Symbol} {l : List Symbol} :
    tm.HaltsOn l ↔ tm.HaltsFrom (tm.initCfg l) :=
  Iff.rfl

/-- **One step of a single-tape Turing machine.** Let $M$ be a single-tape Turing machine, $q$ a
state of $M$ other than the halting state and $t$ a tape, and let the transition function of $M$
at $q$ and the symbol under the head of $t$ (possibly blank) give the symbol $s$ to write
(possibly blank), the head movement $d$ (left, right or none) and the next state $q'$ (possibly
the halting state). Then the configuration in state $q$ with tape $t$ has a successor, namely the
configuration in state $q'$ whose tape is obtained from $t$ by writing $s$ under the head and
then moving the head by $d$. -/
theorem step_some (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.step ⟨some q, t⟩ =
      some ⟨(tm.tr q t.head).2, (t.write (tm.tr q t.head).1.symbol).optionMove
        (tm.tr q t.head).1.movement⟩ :=
  rfl

/-- **A machine that produces an output halts.** If a single-tape Turing machine $M$ outputs a word
$w'$ on an input word $w$, then $M$ halts on $w$. -/
theorem Outputs.haltsOn {tm : SingleTapeTM Symbol} {l l' : List Symbol} (h : tm.Outputs l l') :
    tm.HaltsOn l :=
  ⟨_, h, rfl⟩

/-- **Single-tape Turing machines are deterministic.** For a single-tape Turing machine $M$, every
configuration of $M$ has at most one successor under the transition relation of $M$. -/
theorem rightUnique_transitionRelation (tm : SingleTapeTM Symbol) :
    Relator.RightUnique tm.TransitionRelation := fun _ _ _ h₁ h₂ ↦
  Option.some_injective _ (h₁.symm.trans h₂)

/-- **Halting configurations are exactly those without a successor.** For a single-tape Turing
machine $M$ and a configuration $c$ of $M$, one step of $M$ from $c$ gives no configuration if
and only if $c$ is in the halting state. -/
theorem step_eq_none_iff {tm : SingleTapeTM Symbol} {c : tm.Cfg} :
    tm.step c = none ↔ c.state = none := by
  obtain ⟨_ | q, t⟩ := c
  · simp
  · simp

/-- **Halting from a configuration is normalizability.** Let $M$ be a single-tape Turing machine
and $c$ a configuration of $M$. Then $M$ halts from $c$ if and only if $c$ is normalizable for
the transition relation of $M$, that is, the run of $M$ from $c$ reaches, in finitely many steps
(possibly none), a configuration that has no successor.

The configurations without a successor are exactly those in the halting state. -/
theorem haltsFrom_iff_normalizable {tm : SingleTapeTM Symbol} {c : tm.Cfg} :
    tm.HaltsFrom c ↔ Normalizable tm.TransitionRelation c := by
  have hnormal (d : tm.Cfg) : Normal tm.TransitionRelation d ↔ d.state = none := by
    rw [← step_eq_none_iff, Option.eq_none_iff_forall_ne_some]
    simp only [Normal, Reducible, TransitionRelation, not_exists]
  simp only [HaltsFrom, Normalizable, hnormal]

/-- **Halting from a configuration is invariant along a run.** Let $M$ be a single-tape Turing
machine and let $a$ and $b$ be configurations of $M$ such that the run of $M$ from $a$ reaches $b$
in finitely many steps (possibly none). Then $M$ halts from $a$ if and only if $M$ halts from $b$.

The backward direction holds for any relation; the forward direction uses that $M$ is
deterministic. -/
theorem haltsFrom_iff_of_reflTransGen {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : ReflTransGen tm.TransitionRelation a b) : tm.HaltsFrom a ↔ tm.HaltsFrom b := by
  refine ⟨fun ⟨c, hc, hs⟩ ↦ ?_, fun ⟨c, hc, hs⟩ ↦ ⟨c, h.trans hc, hs⟩⟩
  rcases hc.total_of_right_unique tm.rightUnique_transitionRelation h with h' | h'
  · rcases h'.cases_head with rfl | ⟨_, hstep, -⟩
    · exact ⟨c, .refl, hs⟩
    · obtain ⟨_ | _, _⟩ := c
      · cases hstep
      · cases hs
  · exact ⟨c, h', hs⟩

/-- **Configurations with the same successor halt together.** Let $M$ be a single-tape Turing
machine and let $a$ and $b$ be configurations of $M$ that have the same successor, or that both
have no successor. Then $M$ halts from $a$ if and only if $M$ halts from $b$. -/
theorem haltsFrom_iff_of_step_eq {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : tm.step a = tm.step b) : tm.HaltsFrom a ↔ tm.HaltsFrom b := by
  rcases hb : tm.step b with _ | c
  · have ha : a.state = none := step_eq_none_iff.mp (h.trans hb)
    exact iff_of_true ⟨a, .refl, ha⟩ ⟨b, .refl, step_eq_none_iff.mp hb⟩
  · rw [haltsFrom_iff_of_reflTransGen (ReflTransGen.single (show tm.TransitionRelation a c from
      h.trans hb)), haltsFrom_iff_of_reflTransGen (ReflTransGen.single hb)]

omit [Inhabited Symbol] [Fintype Symbol] in
/-- **Distinct words give distinct tapes.** The map sending a word $w$ to the tape that holds $w$
from the head position rightwards, every other cell blank, is injective. -/
theorem mk₁_injective : Function.Injective (BiTape.mk₁ : List Symbol → BiTape Symbol) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil => cases l₂ with
    | nil => rfl
    | cons b t => exact absurd (congrArg BiTape.head h) (by simp [BiTape.mk₁, BiTape.nil])
  | cons a s => cases l₂ with
    | nil => exact absurd (congrArg BiTape.head h) (by simp [BiTape.mk₁, BiTape.nil])
    | cons b t =>
      have hh := congrArg BiTape.head h
      have hr := congrArg (fun B : BiTape Symbol ↦ B.right.toList) h
      simp only [BiTape.mk₁, Option.some.injEq] at hh hr
      simp only [StackTape.mapSome] at hr
      rw [hh, List.map_injective_iff.mpr (Option.some_injective _) hr]

/-- **Outputs are unique.** If a single-tape Turing machine $M$ outputs the word $l_1$ on the
input $l$ and also outputs the word $l_2$ on the input $l$, then $l_1 = l_2$. Here $M$ outputs a
word $w$ on $l$ when its run from the initial configuration on $l$ halts with exactly $w$ on the
tape, every other cell blank and the head on the first symbol of $w$ (an all-blank tape if $w$ is
empty).

The run of a machine is determined by its input, and a halting configuration has no successor. -/
theorem Outputs.unique {tm : SingleTapeTM Symbol} {l l₁ l₂ : List Symbol} (h₁ : tm.Outputs l l₁)
    (h₂ : tm.Outputs l l₂) : l₁ = l₂ := by
  have halted : ∀ {l' : List Symbol} {c : tm.Cfg},
      ReflTransGen tm.TransitionRelation (tm.haltCfg l') c → c = tm.haltCfg l' := fun h ↦ by
    rcases h.cases_head with h | ⟨_, hs, -⟩
    · exact h.symm
    · simp [TransitionRelation, step, haltCfg] at hs
  have key : tm.haltCfg l₁ = tm.haltCfg l₂ := by
    rcases h₁.total_of_right_unique tm.rightUnique_transitionRelation h₂ with h | h
    · exact (halted h).symm
    · exact halted h
  exact mk₁_injective (congrArg Cfg.BiTape key)

end Cslib.Turing.SingleTapeTM

namespace Cslib.Decidability

open Computability Encodable Cslib.Turing

variable {α : Type*} [Primcodable α]

/-- **Predicates decidable by a single-tape Turing machine.** Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$. A predicate $p$ on $\alpha$ is decidable by a
single-tape machine when there are a finite, nonempty tape alphabet $\Sigma$, an injective map
$\iota$ from the bits $\{0, 1\}$ to $\Sigma$ and a single-tape Turing machine $M$ over $\Sigma$
such that for every $a \in \alpha$ there is a bit $b$ for which $M$ outputs the one-symbol word
$\iota(b)$ on the input word obtained by writing the binary encoding of the code of $a$ in
$\mathbb{N}$ letter by letter through $\iota$, and $b = 1$ exactly when $p(a)$ holds. Here $M$
outputs a word $w$ on an input when its run from the input halts with exactly $w$ on the tape,
every other cell blank and the head on the first symbol of $w$. -/
def SingleTapeDecidable (p : α → Prop) : Prop :=
  ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Symbol, ∀ a, ∃ b : Bool,
      tm.Outputs ((encodeNat (encode a)).map ι) [ι b] ∧ (b = true ↔ p a)

/-- **Predicates recognizable by a single-tape Turing machine.** Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$. A predicate $p$ on $\alpha$ is recognizable by a
single-tape machine when there are a finite, nonempty tape alphabet $\Sigma$, an injective map
$\iota$ from the bits $\{0, 1\}$ to $\Sigma$ and a single-tape Turing machine $M$ over $\Sigma$
such that for every $a \in \alpha$, the run of $M$ on the input word obtained by writing the
binary encoding of the code of $a$ in $\mathbb{N}$ letter by letter through $\iota$ reaches the
halting state if and only if $p(a)$ holds. -/
def SingleTapeRecognizable (p : α → Prop) : Prop :=
  ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Symbol,
      ∀ a, tm.HaltsOn ((encodeNat (encode a)).map ι) ↔ p a

/-- **Co-recognizability by single-tape machines.** Let $\alpha$ be a primcodable type. A predicate
$p$ on $\alpha$ is co-recognizable by a single-tape Turing machine when its complement $\neg p$ is
recognizable by a single-tape Turing machine. -/
def SingleTapeCoRecognizable (p : α → Prop) : Prop :=
  SingleTapeRecognizable fun a ↦ ¬p a

end Cslib.Decidability
