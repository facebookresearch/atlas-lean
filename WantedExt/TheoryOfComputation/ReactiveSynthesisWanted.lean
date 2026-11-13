/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reactive synthesis for deterministic parity specifications (Church's problem)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Games.Parity
public import CSLibExt.Foundations.Data.OmegaSequence.Parity

@[expose] public section

namespace Cslib.ReactiveSynthesisWanted

open Cslib.Games
open Cslib.Games.ParityGame

/-!
# Reactive synthesis for deterministic parity specifications (Church's problem)

Church's problem asks whether a deterministic parity specification, an
automaton reading input/output letter pairs, can be realized by a transducer:
a strategy that, reading the input letters one by one, produces output letters
so that the resulting paired run satisfies the parity condition. The
specification is realizable exactly when the even player (the controller) wins
the associated synthesis parity game from the initial specification state: in
the game the odd player (the environment) picks the next input letter and the
even player picks the next output letter. The specification ranges over
finite state, input, and output types, so the game is a finite parity game
and positional determinacy applies.
-/

/-- A deterministic parity specification: a deterministic automaton reading
input/output letter pairs, with a priority for each state. -/
structure DetParitySpec (Q I O : Type*) where
  /-- The initial state. -/
  start : Q
  /-- The deterministic transition function. -/
  trans : Q → I → O → Q
  /-- The priority of each state. -/
  priority : Q → ℕ

variable {Q I O : Type*}

namespace DetParitySpec

/-- The run of a specification on an input word and an output word. -/
def run (spec : DetParitySpec Q I O) (wIn : ℕ → I) (wOut : ℕ → O) : ℕ → Q
  | 0 => spec.start
  | n + 1 => spec.trans (run spec wIn wOut n) (wIn n) (wOut n)

end DetParitySpec

/-- A transducer `T` realizes a specification when, for every input word, the
paired run with outputs `T` of the input history satisfies the parity
condition. The output at time `k` may depend on the first `k + 1` input
letters (inputs `0` through `k`, inclusive): in the synthesis game the
environment reveals the input letter `k` before the controller chooses the
output letter `k`, so the transducer sees the current input as well as the
history. -/
def Realizes (spec : DetParitySpec Q I O) (T : List I → O) : Prop :=
  ∀ wIn : ℕ → I,
    Cslib.ωSequence.ParityEven
      (((DetParitySpec.run spec wIn (fun k => T ((List.range (k + 1)).map wIn)) :
        ℕ → Q) : ωSequence Q).map spec.priority)

/-- The synthesis parity game of a specification: positions are specification
states (the environment to move, picking the next input letter) and
specification-state/input pairs (the controller to move, picking the next
output letter). -/
def synthesisGame [Inhabited I] [Inhabited O] (spec : DetParitySpec Q I O) :
    ParityGame (Q ⊕ (Q × I)) where
  owner pos := match pos with
    | .inl _ => Player.odd
    | .inr _ => Player.even
  Move pos pos' := match pos, pos' with
    | .inl q, .inr (q', _) => q' = q
    | .inr (q, i), .inl q' => ∃ o, q' = spec.trans q i o
    | _, _ => False
  priority pos := match pos with
    | .inl q => spec.priority q
    | .inr (q, _) => spec.priority q
  serial pos := by
    cases pos with
    | inl q => exact ⟨Sum.inr (q, default), rfl⟩
    | inr p =>
      obtain ⟨q, i⟩ := p
      exact ⟨Sum.inl (spec.trans q i default), ⟨default, rfl⟩⟩

/-- Source: A. Church, "Logic, arithmetic, and automata", *Proceedings of the
International Congress of Mathematicians 1962*, 23-35 (the synthesis problem);
J. R. Büchi and L. H. Landweber, "Solving sequential conditions by finite-state
strategies", *Transactions of the AMS* 138 (1969), 295-311 (decidability via
parity games). -/
public theorem_wanted church_synthesis_wanted :
    ∀ {Q I O : Type*} [Fintype Q] [Fintype I] [Fintype O] [Inhabited I] [Inhabited O]
      (spec : DetParitySpec Q I O),
      (∃ T : List I → O, Realizes spec T) ↔
        Sum.inl spec.start ∈ (synthesisGame spec).WinningRegion Player.even

end Cslib.ReactiveSynthesisWanted
