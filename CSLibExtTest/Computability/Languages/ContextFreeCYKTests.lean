/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CYK

/-!
# Tests for the CYK recognizer

* `anbn`: `S → A X | A B`, `X → S B`, `A → true`, `B → false`, in Chomsky normal form, generates
  `trueⁿ falseⁿ` for `n ≥ 1`. The recognizer accepts `[true, false]` and
  `[true, true, false, false]` and rejects `[]`, `[true, false, false]` and `[false, true]`; by
  `cykAccepts_iff` these are statements about the language.
* `epsAB`: `S → ε | A B`, `A → true`, `B → false` generates `{[], [true, false]}`, so the empty
  word is accepted through `S → ε`.
-/

@[expose] public section

namespace Cslib.Language.CYKTests

/-- `S → A X | A B`, `X → S B`, `A → true`, `B → false`, with `S, X, A, B = 0, 1, 2, 3`. -/
def anbn : ContextFreeGrammar Bool where
  NT := Fin 4
  initial := 0
  rules := {⟨0, [.nonterminal 2, .nonterminal 1]⟩, ⟨0, [.nonterminal 2, .nonterminal 3]⟩,
    ⟨1, [.nonterminal 0, .nonterminal 3]⟩, ⟨2, [.terminal true]⟩, ⟨3, [.terminal false]⟩}

instance : DecidableEq anbn.NT := inferInstanceAs (DecidableEq (Fin 4))
instance : Fintype anbn.NT := inferInstanceAs (Fintype (Fin 4))

theorem anbn_isChomskyNormalForm : IsChomskyNormalForm anbn := by
  unfold IsChomskyNormalForm
  decide

example : cykAccepts anbn [true, false] = true := by decide
example : cykAccepts anbn [true, true, false, false] = true := by decide
example : cykAccepts anbn [] = false := by decide
example : cykAccepts anbn [true, false, false] = false := by decide
example : cykAccepts anbn [false, true] = false := by decide

example : [true, true, false, false] ∈ anbn.language :=
  (cykAccepts_iff anbn_isChomskyNormalForm).1 (by decide)

example : [true, false, false] ∉ anbn.language := fun h => by
  have := (cykAccepts_iff anbn_isChomskyNormalForm).2 h
  revert this
  decide

/-- `S → ε | A B`, `A → true`, `B → false`, with `S, A, B = 0, 1, 2`. -/
def epsAB : ContextFreeGrammar Bool where
  NT := Fin 3
  initial := 0
  rules := {⟨0, []⟩, ⟨0, [.nonterminal 1, .nonterminal 2]⟩, ⟨1, [.terminal true]⟩,
    ⟨2, [.terminal false]⟩}

instance : DecidableEq epsAB.NT := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype epsAB.NT := inferInstanceAs (Fintype (Fin 3))

theorem epsAB_isChomskyNormalForm : IsChomskyNormalForm epsAB := by
  unfold IsChomskyNormalForm
  decide

example : [] ∈ epsAB.language := (cykAccepts_iff epsAB_isChomskyNormalForm).1 (by decide)
example : cykAccepts epsAB [true, false] = true := by decide
example : cykAccepts epsAB [true, false, true, false] = false := by decide

end Cslib.Language.CYKTests
