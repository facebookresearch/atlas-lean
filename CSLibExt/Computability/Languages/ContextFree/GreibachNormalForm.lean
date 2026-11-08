/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# Greibach normal form

A grammar is in Greibach normal form when every production has output
either a single terminal followed by a (possibly empty) string of
nonterminals, or the empty word with the initial nonterminal on the
left; and either the initial nonterminal occurs in no output (so an
empty production cannot leak the empty word to other nonterminals) or
there are no empty outputs at all. Every context-free grammar has an
equivalent grammar in Greibach normal form; that existence theorem is not
formalized here. The standard route is Chomsky normal form, then elimination of left
recursion and substitution.

## Main definitions

* `Cslib.Language.IsGreibachNormalForm`: the normal-form predicate.

## Main results

* `Cslib.Language.exists_terminal_head_of_output_ne_nil`: in Greibach
  normal form, every nonempty production output begins with a terminal
  followed by nonterminals.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {g : ContextFreeGrammar T}

/-- A grammar is in Greibach normal form when every production has
output either a single terminal followed by nonterminals, or the
empty word with the initial nonterminal on the left; and either the
initial nonterminal occurs in no output (so an empty production
cannot leak the empty word to other nonterminals) or there are no
empty outputs at all.
Source: Hopcroft and Ullman, Introduction to Automata Theory,
Languages, and Computation, Addison-Wesley, 1979, Chapter 7
(Greibach normal form); Harrison, Introduction to Formal Language
Theory, Addison-Wesley, 1978, Chapter 4. -/
def IsGreibachNormalForm (g : ContextFreeGrammar T) : Prop :=
  (∀ r ∈ g.rules,
    (r.output = [] ∧ r.input = g.initial) ∨
      ∃ (a : T) (α : List g.NT),
        r.output = Symbol.terminal a :: α.map Symbol.nonterminal) ∧
  ((∀ r ∈ g.rules, Symbol.nonterminal g.initial ∉ r.output) ∨
    ∀ r ∈ g.rules, r.output ≠ [])

/-- In Greibach normal form, every nonempty production output begins
with a terminal followed by nonterminals.
Source: Hopcroft and Ullman, Introduction to Automata Theory,
Languages, and Computation, Addison-Wesley, 1979, Chapter 7
(Greibach normal form); Harrison, Introduction to Formal Language
Theory, Addison-Wesley, 1978, Chapter 4. -/
theorem exists_terminal_head_of_output_ne_nil
    (hg : IsGreibachNormalForm g) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) (hne : r.output ≠ []) :
    ∃ (a : T) (α : List g.NT),
      r.output = Symbol.terminal a :: α.map Symbol.nonterminal := by
  rcases hg.1 r hr with ⟨h0, -⟩ | h
  · exact absurd h0 hne
  · exact h

end Cslib.Language
