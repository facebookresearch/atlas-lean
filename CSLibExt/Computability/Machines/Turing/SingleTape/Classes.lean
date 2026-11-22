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

/-- `tm` **halts** on the input `l`: its run from `initCfg l` reaches a configuration in the
halting state (`state = none`). -/
def HaltsOn (tm : SingleTapeTM Symbol) (l : List Symbol) : Prop :=
  ∃ c : tm.Cfg, ReflTransGen tm.TransitionRelation (tm.initCfg l) c ∧ c.state = none

/-- `tm` **halts from** the configuration `c`: its run from `c` reaches a configuration in the
halting state. This is CSLib's `Relation.Normalizable tm.TransitionRelation c`, the halting
configurations being the normal forms (`haltsFrom_iff_normalizable`), as for CSLib's register
machines (`URM.halts_iff_normalizable`). -/
def HaltsFrom (tm : SingleTapeTM Symbol) (c : tm.Cfg) : Prop :=
  ∃ c' : tm.Cfg, ReflTransGen tm.TransitionRelation c c' ∧ c'.state = none

/-- Halting on an input is halting from its initial configuration. -/
theorem haltsOn_iff_haltsFrom {tm : SingleTapeTM Symbol} {l : List Symbol} :
    tm.HaltsOn l ↔ tm.HaltsFrom (tm.initCfg l) :=
  Iff.rfl

/-- One step from a running state: write, move, and change state as the transition function
says. -/
theorem step_some (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.step ⟨some q, t⟩ =
      some ⟨(tm.tr q t.head).2, (t.write (tm.tr q t.head).1.symbol).optionMove
        (tm.tr q t.head).1.movement⟩ :=
  rfl

/-- A machine that outputs something halts. -/
theorem Outputs.haltsOn {tm : SingleTapeTM Symbol} {l l' : List Symbol} (h : tm.Outputs l l') :
    tm.HaltsOn l :=
  ⟨_, h, rfl⟩

/-- A single-tape machine is deterministic: a configuration has at most one successor. -/
theorem rightUnique_transitionRelation (tm : SingleTapeTM Symbol) :
    Relator.RightUnique tm.TransitionRelation := fun _ _ _ h₁ h₂ ↦
  Option.some_injective _ (h₁.symm.trans h₂)

/-- A configuration has no successor iff it is in the halting state. -/
theorem step_eq_none_iff {tm : SingleTapeTM Symbol} {c : tm.Cfg} :
    tm.step c = none ↔ c.state = none := by
  obtain ⟨_ | q, t⟩ := c
  · simp
  · simp

/-- **Halting from a configuration is normalizability** of the transition relation: the
configurations without a successor are those in the halting state. -/
theorem haltsFrom_iff_normalizable {tm : SingleTapeTM Symbol} {c : tm.Cfg} :
    tm.HaltsFrom c ↔ Normalizable tm.TransitionRelation c := by
  have hnormal (d : tm.Cfg) : Normal tm.TransitionRelation d ↔ d.state = none := by
    rw [← step_eq_none_iff, Option.eq_none_iff_forall_ne_some]
    simp only [Normal, Reducible, TransitionRelation, not_exists]
  simp only [HaltsFrom, Normalizable, hnormal]

/-- **Halting from a configuration is invariant along a run**: backwards for any relation, and
forwards because the machine is deterministic. -/
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

/-- Two configurations with the same successor, or both without one, both halt or both do
not. -/
theorem haltsFrom_iff_of_step_eq {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : tm.step a = tm.step b) : tm.HaltsFrom a ↔ tm.HaltsFrom b := by
  rcases hb : tm.step b with _ | c
  · have ha : a.state = none := step_eq_none_iff.mp (h.trans hb)
    exact iff_of_true ⟨a, .refl, ha⟩ ⟨b, .refl, step_eq_none_iff.mp hb⟩
  · rw [haltsFrom_iff_of_reflTransGen (ReflTransGen.single (show tm.TransitionRelation a c from
      h.trans hb)), haltsFrom_iff_of_reflTransGen (ReflTransGen.single hb)]

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Distinct words are laid out as distinct tapes. -/
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

/-- **Outputs are unique**: the run of a machine is determined by its input, and a halting
configuration has no successor. -/
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

/-- `p` is **decidable by a single-tape machine**: for some finite tape alphabet `Symbol` with
an injective copy `ι` of the input bits, some `SingleTapeTM` outputs `[ι b]` on the input word
`(encodeNat (encode a)).map ι`, every other cell blank, with `b = true` exactly when `p a`. -/
def SingleTapeDecidable (p : α → Prop) : Prop :=
  ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Symbol, ∀ a, ∃ b : Bool,
      tm.Outputs ((encodeNat (encode a)).map ι) [ι b] ∧ (b = true ↔ p a)

/-- `p` is **recognizable by a single-tape machine**: for some finite tape alphabet `Symbol`
with an injective copy `ι` of the input bits, some `SingleTapeTM` halts on the input word
`(encodeNat (encode a)).map ι` exactly when `p a`. -/
def SingleTapeRecognizable (p : α → Prop) : Prop :=
  ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Symbol,
      ∀ a, tm.HaltsOn ((encodeNat (encode a)).map ι) ↔ p a

/-- `p` is **co-recognizable by a single-tape machine**: its complement is recognizable. -/
def SingleTapeCoRecognizable (p : α → Prop) : Prop :=
  SingleTapeRecognizable fun a ↦ ¬p a

end Cslib.Decidability
