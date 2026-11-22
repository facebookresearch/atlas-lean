/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Closure
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod

/-!
# Regular languages are context-free

The right-linear grammar of a DFA: states are the nonterminals, a transition
on `a` from `q` becomes `q → a (step q a)`, and accepting states erase. The
valuation of a state is the language the DFA accepts from that state.

The finite-alphabet assumption is essential: a context-free grammar has
finitely many productions, hence mentions only finitely many terminals,
whereas a DFA over an infinite alphabet can accept every one-letter word.

## Main results

* `Cslib.Language.IsRegular.isContextFree`: over a finite alphabet, every
  regular language is context-free.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T : Type*} {σ : Type}

/-- The right-linear grammar of a DFA, over a finite alphabet. -/
private noncomputable abbrev dfaGrammar (M : DFA T σ) [Fintype σ] [Fintype T] :
    ContextFreeGrammar T where
  NT := σ
  initial := M.start
  rules :=
    (Finset.univ.image fun (qa : σ × T) =>
        (⟨qa.1, [Symbol.terminal qa.2, Symbol.nonterminal (M.step qa.1 qa.2)]⟩ :
          ContextFreeRule T σ))
      ∪ ((Finset.univ.filter fun q => q ∈ M.accept).image fun q =>
          (⟨q, []⟩ : ContextFreeRule T σ))

private theorem isValuation_dfaGrammar (M : DFA T σ) [Fintype σ] [Fintype T] :
    IsValuation (dfaGrammar M) M.acceptsFrom := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨⟨q, a⟩, -, hrfl⟩ := Finset.mem_image.mp hr
    subst hrfl
    intro w hw
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
    obtain ⟨x', hx', y', hy', hxy'⟩ := Language.mem_mul.mp hy
    simp only [evalSymbol_terminal] at hx
    subst hx
    have hy_nil : y' = [] := by simpa using hy'
    subst hy_nil
    simp only [List.append_nil] at hxy'
    subst hxy'
    subst hxy
    simp only [evalSymbol_nonterminal] at hx'
    exact hx'
  · obtain ⟨q, hq, hrfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter] at hq
    subst hrfl
    intro w hw
    have hw0 : w = [] := hw
    subst hw0
    exact hq.2

private theorem derives_dfaGrammar (M : DFA T σ) [Fintype σ] [Fintype T]
    (q : σ) (w : List T) (hw : M.evalFrom q w ∈ M.accept) :
    (dfaGrammar M).Derives [Symbol.nonterminal q] (w.map Symbol.terminal) := by
  induction w generalizing q with
  | nil =>
    refine ContextFreeGrammar.Produces.single ⟨⟨q, []⟩, ?_, ContextFreeRule.Rewrites.input_output⟩
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hw⟩, rfl⟩
  | cons a w ih =>
    rw [DFA.evalFrom_cons] at hw
    have hstep : (dfaGrammar M).Produces [Symbol.nonterminal q]
        [Symbol.terminal a, Symbol.nonterminal (M.step q a)] :=
      ⟨⟨q, [Symbol.terminal a, Symbol.nonterminal (M.step q a)]⟩,
        Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(q, a), Finset.mem_univ (q, a), rfl⟩),
        ContextFreeRule.Rewrites.input_output⟩
    have htail := ih (M.step q a) hw
    have hboth := derives_append (g := dfaGrammar M)
      (ContextFreeGrammar.Derives.refl (g := dfaGrammar M) [Symbol.terminal a]) htail
    simpa using hstep.trans_derives hboth

private theorem dfaGrammar_language (M : DFA T σ) [Fintype σ] [Fintype T] :
    (dfaGrammar M).language = M.accepts := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := dfaGrammar M) (isValuation_dfaGrammar M)
    exact hle
  · intro w hw
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    exact derives_dfaGrammar M M.start w hw

/-- Over a finite alphabet, every regular language is context-free.

Finiteness of the alphabet is necessary: a grammar has finitely many
productions, hence mentions only finitely many terminal symbols, but a DFA
over an infinite alphabet may accept every one-letter word. -/
theorem IsRegular.isContextFree [Finite T] {L : Language T} (hL : L.IsRegular) :
    L.IsContextFree := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  exact ⟨@dfaGrammar T σ M hσ (Fintype.ofFinite T),
    @dfaGrammar_language T σ M hσ (Fintype.ofFinite T)⟩

end Cslib.Language
