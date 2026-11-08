/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Basic

/-!
# Ordinary-client tests for the context-free basic API

These examples use the valuation API and the elementary context-free
languages from outside the defining namespace, so a naming or universe
slip in the public surface is caught here rather than by a downstream file.
-/

public section

namespace Cslib.Language.ContextFreeBasicTests

/-- A terminal sentential form is interpreted as its singleton language. -/
theorem eval_terminal_form (V : Fin 2 → Language ℕ) :
    evalForm V [Symbol.terminal 3, Symbol.terminal 1] = {[3, 1]} := by
  have h := evalForm_map_terminal V [3, 1]
  simpa using h

/-- Interpreting an append of forms multiplies the interpretations. -/
theorem eval_append (V : Fin 2 → Language ℕ) (u v : List (Symbol ℕ (Fin 2))) :
    evalForm V (u ++ v) = evalForm V u * evalForm V v :=
  evalForm_append V u v

/-- The three elementary languages over a concrete alphabet are context-free. -/
theorem zero_cf : (0 : Language ℕ).IsContextFree :=
  IsContextFree.zero

theorem one_cf : (1 : Language ℕ).IsContextFree :=
  IsContextFree.one

theorem singleton_cf : ({[4, 1, 4]} : Language ℕ).IsContextFree :=
  IsContextFree.singleton_word [4, 1, 4]

/-- Generating from the initial nonterminal recovers the grammar's language. -/
theorem from_initial (g : ContextFreeGrammar ℕ) :
    languageFrom g g.initial = g.language :=
  languageFrom_initial

/-- The canonical assignment is a valuation of its own grammar. -/
theorem canonical_valuation (g : ContextFreeGrammar ℕ) :
    IsValuation g (languageFrom g) :=
  isValuation_languageFrom

/-- A grammar's language is bounded by any valuation at its initial symbol. -/
theorem language_bound (g : ContextFreeGrammar ℕ) (V : g.NT → Language ℕ)
    (hV : IsValuation g V) : g.language ≤ V g.initial :=
  language_le_of_valuation hV

/-- One derivation step shrinks an interpretation. -/
theorem step_shrinks (g : ContextFreeGrammar ℕ) (V : g.NT → Language ℕ)
    (hV : IsValuation g V) {u v : List (Symbol ℕ g.NT)} (h : g.Produces u v) :
    evalForm V v ≤ evalForm V u :=
  evalForm_le_of_produces hV h

/-- A full derivation shrinks an interpretation. -/
theorem derivation_shrinks (g : ContextFreeGrammar ℕ) (V : g.NT → Language ℕ)
    (hV : IsValuation g V) {u v : List (Symbol ℕ g.NT)} (h : g.Derives u v) :
    evalForm V v ≤ evalForm V u :=
  evalForm_le_of_derives hV h

/-- Derivations lift along a renaming whose image rules are available. -/
theorem rename_lift (g G : ContextFreeGrammar ℕ) (f : g.NT → G.NT)
    (hsub : ∀ r ∈ g.rules, mapRule f r ∈ G.rules)
    {u v : List (Symbol ℕ g.NT)} (h : g.Derives u v) :
    G.Derives (u.map (mapSymbol f)) (v.map (mapSymbol f)) :=
  derives_map_of_forall_mem hsub h

/-- Renaming commutes with interpreting a sentential form. -/
theorem eval_rename (V : Fin 3 → Language ℕ) (f : Fin 2 → Fin 3)
    (u : List (Symbol ℕ (Fin 2))) :
    evalForm V (u.map (mapSymbol f)) = evalForm (V ∘ f) u :=
  evalForm_map f V u

/-- A form made of one nonterminal and a rest concatenates its derivation. -/
theorem append_form (g : ContextFreeGrammar ℕ)
    {u u' v v' : List (Symbol ℕ g.NT)} (hu : g.Derives u u') (hv : g.Derives v v') :
    g.Derives (u ++ v) (u' ++ v') :=
  derives_append hu hv

end Cslib.Language.ContextFreeBasicTests
