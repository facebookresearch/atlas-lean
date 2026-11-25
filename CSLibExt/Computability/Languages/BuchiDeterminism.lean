/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Cslib/Computability/Languages/OmegaRegularLanguage.lean` (CSLib):
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.OmegaRegularLanguage

/-!
# Nondeterministic Büchi automata are more expressive than deterministic ones

Upstream CSLib defines the ω-language `Cslib.ωLanguage.Example.eventuallyZero` of the infinite
words over `Fin 2` that are eventually constantly `0`, recognizes it with a two-state
nondeterministic Büchi automaton, and shows that it is not the ω-limit of a regular language
(`Cslib.ωLanguage.Example.eventuallyZero_not_omegaLim`), hence not recognized by a
deterministic Büchi automaton; its theorem `Cslib.ωLanguage.IsRegular.not_da_buchi` only
records that some such ω-regular language exists. This file states the separation for this
specific language, as in Vardi's Proposition 8 (whose language `(0 + 1)* 1^ω` is the same up
to exchanging the two letters). The proof of `not_exists_da_buchi_eventuallyZero` is the
second half of the proof of upstream `Cslib.ωLanguage.IsRegular.not_da_buchi`, copied from
CSLib; the converse inclusion (every deterministic Büchi language is a nondeterministic one)
is upstream `Cslib.Automata.DA.Buchi.toNABuchi_language_eq`.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Section 2.2, Proposition 8 (author's posted version `banff94rj.pdf`).
-/

@[expose] public section

namespace Cslib.ωLanguage.Example

open Automata Automata.ωAcceptor

/-- **No deterministic Büchi automaton accepts "eventually always 0".** No deterministic Büchi
automaton over `Fin 2`, with any set of states, finite or not, accepts exactly the infinite words
that are eventually constantly `0` (Vardi, "An automata-theoretic approach to linear temporal
logic", LNCS 1043, 1996, Proposition 8, for `(0 + 1)* 1^ω`, the same language with the letters
exchanged). The proof is the one of upstream `Cslib.ωLanguage.IsRegular.not_da_buchi`. -/
theorem not_exists_da_buchi_eventuallyZero :
    ¬ ∃ (State : Type) (da : DA.Buchi State (Fin 2)), language da = eventuallyZero := by
  rintro ⟨State, ⟨da, acc⟩, h⟩
  have := eventuallyZero_not_omegaLim
  grind [DA.buchi_eq_finAcc_omegaLim]

/-- **Nondeterministic Büchi automata are strictly more expressive than deterministic ones.**
Every deterministic Büchi automaton over `Fin 2` has a nondeterministic Büchi automaton with
the same states and language, while the language of the infinite words over `Fin 2` that are
eventually constantly `0` is accepted by a nondeterministic Büchi automaton with two states
but by no deterministic Büchi automaton (Vardi, "An automata-theoretic approach to linear
temporal logic", LNCS 1043, 1996, Proposition 8 and the automaton before it). The inclusion
is upstream `Cslib.Automata.DA.Buchi.toNABuchi_language_eq`. -/
theorem nondeterministic_buchi_strictly_more_expressive :
    (∀ (State : Type) (da : DA.Buchi State (Fin 2)),
      ∃ na : NA.Buchi State (Fin 2), language na = language da) ∧
    (∃ na : NA.Buchi (Fin 2) (Fin 2), language na = eventuallyZero) ∧
      ¬ ∃ (State : Type) (da : DA.Buchi State (Fin 2)), language da = eventuallyZero :=
  ⟨fun _ da => ⟨da.toNABuchi, DA.Buchi.toNABuchi_language_eq⟩,
    ⟨eventuallyZeroNa, eventuallyZero_accepted_by_na_buchi⟩, not_exists_da_buchi_eventuallyZero⟩

end Cslib.ωLanguage.Example
