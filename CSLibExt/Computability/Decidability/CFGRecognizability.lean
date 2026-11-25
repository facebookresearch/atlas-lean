/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recognizability of PCP and of problems about context-free grammars
-/
module

public import CSLibExt.Computability.Decidability.PCPApplications
public import CSLibExt.Computability.Decidability.ContextFree
public import MathlibExt.Computability.RE

/-!
# Recognizability of PCP and of problems about context-free grammars

PCP is recognizable (`Post.tm2Recognizable_pcp`) but undecidable, so by Post's theorem its
complement is not recognizable (`exists_not_tm2Recognizable_not_pcp`). Membership in a
context-free language is decidable (`EncodedCFG.tm2Decidable_mem_language`), so searching over
words shows:

* whether two context-free languages intersect (`OVERLAP_CFG`) is recognizable
  (`tm2Recognizable_overlap`), and disjointness is not (`exists_not_tm2Recognizable_disjoint`);
* universality (`ALL_CFG`), equivalence (`EQ_CFG`) and inclusion are co-recognizable
  (`tm2CoRecognizable_univ`, `tm2CoRecognizable_language_eq`, `tm2CoRecognizable_language_le`),
  but not recognizable: the complement of PCP reduces to universality, and universality to the
  other two (`exists_not_tm2Recognizable_univ`, `exists_not_tm2Recognizable_language_eq`,
  `exists_not_tm2Recognizable_language_le`).

## Main results

- `not_tm2Recognizable_not_of`, `exists_not_tm2Recognizable_not_pcp`.
- `tm2Recognizable_overlap`, `exists_not_tm2Recognizable_disjoint`.
- `tm2CoRecognizable_univ`, `exists_not_tm2Recognizable_univ`, and the same for
  `language_eq` and `language_le`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §4.2 (Post's
  theorem: decidable iff recognizable and co-recognizable) and §5.1–5.2.
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Cslib.Language Grammar Post

/-- **Post's theorem, contrapositive**: a recognizable undecidable predicate has an
unrecognizable complement. -/
theorem not_tm2Recognizable_not_of {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : TM2Recognizable p) (hd : ¬TM2Decidable p) : ¬TM2Recognizable fun a ↦ ¬p a :=
  fun hn ↦ hd (tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable.mpr ⟨hp, hn⟩)

/-- **The complement of PCP is not recognizable**, over some finite alphabet. -/
theorem exists_not_tm2Recognizable_not_pcp :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
      ¬TM2Recognizable fun P : List (Domino α) ↦ ¬PCP P := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_pcp
  classical
  exact ⟨α, inferInstance, inferInstance, not_tm2Recognizable_not_of tm2Recognizable_pcp h⟩

/-! ### Searching over words -/

section Membership

variable {T : Type} [Primcodable T] [DecidableEq T]

theorem computablePred_mem_language :
    ComputablePred fun p : EncodedCFG T × List T ↦ p.2 ∈ p.1.language :=
  tm2Decidable_iff_computablePred.mp EncodedCFG.tm2Decidable_mem_language

/-- **Membership in the first grammar of a pair is computable.** Let $T$ be an alphabet with a
primcodable encoding and decidable equality. The predicate that holds of a pair
$((g_1, g_2), w)$, where $g_1, g_2$ are encoded context-free grammars over $T$ and $w$ is a word
over $T$, exactly when $w$ lies in the language of $g_1$, is a computable predicate. -/
theorem computablePred_mem_fst :
    ComputablePred fun p : (EncodedCFG T × EncodedCFG T) × List T ↦ p.2 ∈ p.1.1.language :=
  ComputablePred.computable_of_manyOneReducible
    ⟨_, Computable.pair (Computable.fst.comp Computable.fst) Computable.snd, fun _ ↦ Iff.rfl⟩
    computablePred_mem_language

theorem computablePred_mem_snd :
    ComputablePred fun p : (EncodedCFG T × EncodedCFG T) × List T ↦ p.2 ∈ p.1.2.language :=
  ComputablePred.computable_of_manyOneReducible
    ⟨_, Computable.pair (Computable.snd.comp Computable.fst) Computable.snd, fun _ ↦ Iff.rfl⟩
    computablePred_mem_language

/-- **The overlap problem for context-free grammars is recognizable.** Let $T$ be an alphabet
with a primitive recursive coding into the natural numbers and decidable equality. For an
encoded context-free grammar $G$ over $T$, write $L(G)$ for the language it generates. The
problem $\mathrm{OVERLAP}_{\mathrm{CFG}}$, the set of pairs $(G, H)$ of encoded context-free
grammars over $T$ such that some word $w$ over $T$ lies in both $L(G)$ and $L(H)$, is
recognizable by a multi-stack machine.

The proof searches for a common word, using that membership in a context-free language is
decidable. -/
theorem tm2Recognizable_overlap :
    TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  tm2Recognizable_iff_rePred.mpr <| MetaMathlibExt.REPred.exists
    (R := fun (g : EncodedCFG T × EncodedCFG T) (w : List T) ↦
      w ∈ g.1.language ∧ w ∈ g.2.language)
    (MetaMathlibExt.ComputablePred.and computablePred_mem_fst computablePred_mem_snd).to_re

/-- **Universality of context-free grammars is co-recognizable.** For every alphabet $T$ with a
primcodable encoding and decidable equality, the set of encoded context-free grammars over $T$
whose language contains every word over $T$ is co-recognizable by a multi-stack Turing machine.

A recognizer for the complement searches for a word outside the language. -/
theorem tm2CoRecognizable_univ :
    TM2CoRecognizable fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language :=
  tm2CoRecognizable_iff_rePred_not.mpr <| (MetaMathlibExt.REPred.exists
    (R := fun (g : EncodedCFG T) (w : List T) ↦ ¬w ∈ g.language)
    computablePred_mem_language.not.to_re).of_eq
    fun _ ↦ not_forall.symm

/-- **Equivalence of context-free grammars is co-recognizable.** For every alphabet $T$ with a
primcodable encoding and decidable equality, the set of pairs $(g_1, g_2)$ of encoded
context-free grammars over $T$ whose languages are equal is co-recognizable by a multi-stack
Turing machine.

A recognizer for the complement searches for a word in exactly one of the two languages. -/
theorem tm2CoRecognizable_language_eq :
    TM2CoRecognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language = g.2.language := by
  refine tm2CoRecognizable_iff_rePred_not.mpr <| (MetaMathlibExt.REPred.exists
    (R := fun (g : EncodedCFG T × EncodedCFG T) (w : List T) ↦
      (w ∈ g.1.language ∧ ¬w ∈ g.2.language) ∨ (¬w ∈ g.1.language ∧ w ∈ g.2.language))
    (MetaMathlibExt.ComputablePred.or
      (MetaMathlibExt.ComputablePred.and computablePred_mem_fst computablePred_mem_snd.not)
      (MetaMathlibExt.ComputablePred.and computablePred_mem_fst.not computablePred_mem_snd)).to_re
    ).of_eq fun g ↦ ?_
  constructor
  · rintro ⟨w, hw⟩ heq
    rw [heq] at hw
    tauto
  · intro hne
    by_contra hall
    push Not at hall
    exact hne (Set.ext fun w ↦ by have := hall w; tauto)

/-- **Inclusion of context-free languages is co-recognizable.** For every alphabet $T$ with a
primcodable encoding and decidable equality, the set of pairs $(g_1, g_2)$ of encoded
context-free grammars over $T$ for which the language of $g_1$ is contained in the language of
$g_2$ is co-recognizable by a multi-stack Turing machine. -/
theorem tm2CoRecognizable_language_le :
    TM2CoRecognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language ≤ g.2.language := by
  refine tm2CoRecognizable_iff_rePred_not.mpr <| (MetaMathlibExt.REPred.exists
    (R := fun (g : EncodedCFG T × EncodedCFG T) (w : List T) ↦
      w ∈ g.1.language ∧ ¬w ∈ g.2.language)
    (MetaMathlibExt.ComputablePred.and computablePred_mem_fst
      computablePred_mem_snd.not).to_re).of_eq fun g ↦ ?_
  constructor
  · rintro ⟨w, h₁, h₂⟩ hle
    exact h₂ (hle h₁)
  · intro h
    by_contra hn
    push Not at hn
    exact h fun w hw ↦ hn w hw

end Membership

/-! ### Unrecognizable problems -/

/-- **Disjointness of context-free languages is not recognizable.** There is an alphabet $T$,
with a primcodable encoding and decidable equality, such that the set of pairs $(g_1, g_2)$ of
encoded context-free grammars over $T$ whose languages are disjoint (no word lies in both) is not
recognizable by a multi-stack Turing machine. -/
theorem exists_not_tm2Recognizable_disjoint :
    ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦
        ∀ w, ¬(w ∈ g.1.language ∧ w ∈ g.2.language) := by
  obtain ⟨T, _, _, h⟩ := exists_not_tm2Decidable_overlap
  refine ⟨T, inferInstance, inferInstance, ?_⟩
  simpa only [not_exists] using not_tm2Recognizable_not_of tm2Recognizable_overlap h

/-- **Universality of context-free grammars is not recognizable.** There is a finite alphabet
$T$, with a primcodable encoding and decidable equality, such that the set of encoded
context-free grammars over $T$ whose language contains every word over $T$ is not recognizable by
a multi-stack Turing machine.

The complement of the Post correspondence problem reduces to this problem. -/
theorem exists_not_tm2Recognizable_univ :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Recognizable fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Recognizable_not_pcp
  classical
  exact ⟨α ⊕ Bool, inferInstance, inferInstance, inferInstance, fun hr ↦
    h (tm2Recognizable_of_manyOneReducible manyOneReducible_not_pcp_univ hr)⟩

/-- **Equivalence of context-free grammars is not recognizable.** There is a finite alphabet
$T$, with a primcodable encoding and decidable equality, such that the set of pairs $(g_1, g_2)$
of encoded context-free grammars over $T$ whose languages are equal is not recognizable by a
multi-stack Turing machine. -/
theorem exists_not_tm2Recognizable_language_eq :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language = g.2.language := by
  obtain ⟨T, _, _, _, h⟩ := exists_not_tm2Recognizable_univ
  refine ⟨T, inferInstance, inferInstance, inferInstance, fun hr ↦ h ?_⟩
  refine tm2Recognizable_of_manyOneReducible ⟨fun g ↦ (g, allWordsCFG),
    (Primrec.pair Primrec.id (Primrec.const _)).to_comp, fun g ↦ ⟨fun hg ↦ ?_, fun hg w ↦ ?_⟩⟩ hr
  · exact Set.ext fun w ↦ ⟨fun _ ↦ mem_language_allWordsCFG w, fun _ ↦ hg w⟩
  · exact (congrArg (w ∈ ·) hg).mpr (mem_language_allWordsCFG w)

/-- **Inclusion of context-free languages is not recognizable.** There is a finite alphabet $T$,
with a primcodable encoding and decidable equality, such that the set of pairs $(g_1, g_2)$ of
encoded context-free grammars over $T$ for which the language of $g_1$ is contained in the
language of $g_2$ is not recognizable by a multi-stack Turing machine. -/
theorem exists_not_tm2Recognizable_language_le :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language ≤ g.2.language := by
  obtain ⟨T, _, _, _, h⟩ := exists_not_tm2Recognizable_univ
  refine ⟨T, inferInstance, inferInstance, inferInstance, fun hr ↦ h ?_⟩
  exact tm2Recognizable_of_manyOneReducible ⟨fun g ↦ (allWordsCFG, g),
    (Primrec.pair (Primrec.const _) Primrec.id).to_comp, fun g ↦ ⟨fun hg w _ ↦ hg w,
      fun hg w ↦ hg (mem_language_allWordsCFG w)⟩⟩ hr

end Cslib.Decidability
