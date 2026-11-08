/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Reduced

/-!
# Ordinary-client tests for reduced grammars
-/

public section

namespace Cslib.Language.ContextFreeReducedTests

/-- The grammar with the single production `S → ε`. -/
abbrev epsOnlyGrammar : ContextFreeGrammar Bool where
  NT := Unit
  initial := ()
  rules := {⟨(), []⟩}

/-- Its only nonterminal is nullable. -/
theorem epsOnly_nullable : Nullable epsOnlyGrammar () := by
  have hr : (⟨(), []⟩ : ContextFreeRule Bool Unit) ∈
      epsOnlyGrammar.rules :=
    Finset.mem_singleton_self _
  exact nullable_of_yields (yields_of_rule hr Yields.nil)

/-- Epsilon-elimination removes the empty word from its language. -/
theorem epsOnly_epsGrammar_not_mem :
    ([] : List Bool) ∉ (epsGrammar epsOnlyGrammar).language :=
  fun h => (epsGrammar_language.mp h).2 rfl

/-- Unit-elimination preserves the language of the epsilon-only
grammar. -/
theorem epsOnly_unitGrammar_language :
    (unitGrammar epsOnlyGrammar).language = epsOnlyGrammar.language :=
  unitGrammar_language

/-- Unit reachability is reflexive, exercised through the public
definition. -/
theorem epsOnly_unitSteps_refl : UnitSteps epsOnlyGrammar () () :=
  Relation.ReflTransGen.refl

/-- The reduced grammar for a singleton language still generates the
singleton word, and has no empty or unit outputs. -/
theorem singleton_reduced :
    ∃ g' : ContextFreeGrammar Bool,
      (∀ w, w ∈ g'.language ↔ w = [true]) ∧
      (∀ r ∈ g'.rules, r.output ≠ []) ∧
      (∀ r ∈ g'.rules, ¬ IsUnitOutput r.output) := by
  obtain ⟨g, hg⟩ := IsContextFree.singleton_word [true]
  obtain ⟨g', hlang, hne, hunit⟩ := exists_reduced_grammar g
  refine ⟨g', ?_, hne, hunit⟩
  intro w
  rw [hlang]
  constructor
  · rintro ⟨hw, -⟩
    rw [hg] at hw
    exact hw
  · rintro rfl
    exact ⟨by rw [hg]; rfl, by simp⟩

end Cslib.Language.ContextFreeReducedTests
