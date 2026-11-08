/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.PDAEquiv

/-!
# Ordinary-client tests for pushdown automata and the PDA<->CFG equivalence
-/

public section

namespace Cslib.Language.ContextFreePDATests

open Automata

/-- Every singleton language is accepted by the simulating PDA. -/
theorem singleton_pda :
    ∃ (g : ContextFreeGrammar ℕ) (M : PDA ℕ Unit (Symbol ℕ g.NT)),
      M.accepts = {[1, 2]} :=
  IsContextFree.exists_pda_accepts (IsContextFree.singleton_word [1, 2])

/-- Every singleton language is accepted by a finitely supported PDA, the
standard finite model. -/
theorem singleton_pda_finitely_supported :
    ∃ (g : ContextFreeGrammar ℕ) (M : PDA ℕ Unit (Symbol ℕ g.NT)),
      M.FinitelySupported ∧ M.accepts = {[1, 2]} :=
  IsContextFree.exists_finitely_supported_pda_accepts
    (IsContextFree.singleton_word [1, 2])

/-- A PDA over `Bool` whose only move pops the initial stack symbol on `ε`. -/
def popPDA : PDA Bool Unit Unit where
  step _ opt _ := match opt with
    | none => {((), [])}
    | some _ => ∅
  start := ()
  startStack := ()

/-- The single `ε`-step popping the initial stack symbol. -/
theorem popPDA_step : popPDA.Step ⟨(), [], [()]⟩ ⟨(), [], []⟩ := by
  have hmem : ((), ([] : List Unit)) ∈ popPDA.step () none () :=
    Finset.mem_singleton_self _
  exact PDA.Step.epsilon hmem

/-- It accepts the empty word by that single `ε`-step. -/
theorem popPDA_accepts_nil : ([] : List Bool) ∈ popPDA.accepts :=
  ⟨(), Relation.ReflTransGen.single popPDA_step⟩

/-- Computations ignore extra bottom-of-stack symbols, exercised through
the public context lemma from the same one-step computation. -/
theorem popPDA_append_stack :
    popPDA.Derives ⟨(), [], [(), ()]⟩ ⟨(), [], [()]⟩ := by
  have hder : popPDA.Derives ⟨(), [], [()]⟩ ⟨(), [], []⟩ :=
    Relation.ReflTransGen.single popPDA_step
  exact hder.append_input_stack [] [()]

/-- `popPDA` consumes no letters, so the empty letter set works. -/
theorem popPDA_no_letters :
    ∀ (p : Unit) (a : Bool) (γ : Unit), a ∉ (∅ : Finset Bool) →
      popPDA.step p (some a) γ = ∅ :=
  fun _ _ _ _ => rfl

/-- The triple grammar of `popPDA` generates its language. -/
theorem popPDA_grammar_language :
    (pdaGrammar popPDA ∅).language = popPDA.accepts :=
  PDA.pdaGrammar_language popPDA_no_letters

/-- The language of `popPDA` is context-free, through the PDA-to-CFG
construction. -/
theorem popPDA_accepts_isContextFree : popPDA.accepts.IsContextFree :=
  PDA.isContextFree_accepts (M := popPDA) (T₀ := ∅) popPDA_no_letters

/-- Restricting `popPDA` to its single stack symbol preserves its
language. -/
theorem popPDA_restrict_accepts :
    (popPDA.restrict {()} (by simp) (by
      intro p opt γ _ y hy γ' hγ'
      cases opt with
      | none =>
        have : y = ((), []) := Finset.mem_singleton.mp hy
        rw [this] at hγ'
        cases hγ'
      | some a => simp [popPDA] at hy)).accepts = popPDA.accepts :=
  PDA.accepts_restrict

/-- The equivalence, exercised forward on a singleton language: some
finite PDA accepts it. -/
theorem singleton_finite_pda :
    ∃ (σ Γ : Type) (_ : Fintype σ) (_ : Fintype Γ) (M : PDA ℕ σ Γ),
      (∃ T₀ : Finset ℕ, ∀ (p : σ) (a : ℕ) (γ : Γ), a ∉ T₀ →
        M.step p (some a) γ = ∅) ∧ M.accepts = {[1, 2]} :=
  isContextFree_iff_exists_pda_accepts.mp
    (IsContextFree.singleton_word [1, 2])

/-- The equivalence, exercised backward: finite-PDA languages are
context-free. -/
theorem finite_pda_language_isContextFree :
    popPDA.accepts.IsContextFree :=
  isContextFree_iff_exists_pda_accepts.mpr
    ⟨Unit, Unit, inferInstance, inferInstance, popPDA,
      ⟨∅, popPDA_no_letters⟩, rfl⟩

end Cslib.Language.ContextFreePDATests
