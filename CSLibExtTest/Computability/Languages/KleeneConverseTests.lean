/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.KleeneConverse
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Client tests for Kleene's theorem, converse direction

Smoke tests applying `Cslib.Language.IsRegular.exists_regex` and
`Cslib.Language.isRegular_iff_exists_regex` to the one-letter-word DFA, plus an
axiom audit for the new API.
-/

set_option autoImplicit false

open Cslib.Language
open scoped Computability

/-- The one-letter-word language over `Bool` is denoted by a regular expression. -/
example : ∃ r : RegularExpression Bool, r.matches' = ({w : List Bool | w.length = 1} : Language Bool) :=
  IsRegular.exists_regex
    ⟨Fin 3, inferInstance, (KleeneConverse.singletonDFA : DFA Bool (Fin 3)),
      KleeneConverse.singletonDFA_accepts⟩

/-- The Kleene iff, applied to the one-letter-word language. -/
example : (KleeneConverse.singletonDFA : DFA Bool (Fin 3)).accepts.IsRegular ↔
    ∃ r : RegularExpression Bool,
      r.matches' = (KleeneConverse.singletonDFA : DFA Bool (Fin 3)).accepts :=
  isRegular_iff_exists_regex

/-- The regular expression for the one-letter-word language matches `[true]` but not
`[]` or `[true, true]`. -/
example : ∃ r : RegularExpression Bool, r.matches' = ({w : List Bool | w.length = 1} : Language Bool) ∧
    [true] ∈ r.matches' ∧ [] ∉ r.matches' ∧ [true, true] ∉ r.matches' := by
  obtain ⟨r, hr⟩ := IsRegular.exists_regex
    ⟨Fin 3, inferInstance, (KleeneConverse.singletonDFA : DFA Bool (Fin 3)),
      KleeneConverse.singletonDFA_accepts⟩
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · rw [hr]
    change (1 : ℕ) = 1
    rfl
  · rw [hr]
    intro h
    change (0 : ℕ) = 1 at h
    exact absurd h (by decide)
  · rw [hr]
    intro h
    change (2 : ℕ) = 1 at h
    exact absurd h (by decide)

#print axioms Cslib.Language.IsRegular.exists_regex
#print axioms Cslib.Language.isRegular_iff_exists_regex
#print axioms Cslib.Language.exists_regular_not_regex
