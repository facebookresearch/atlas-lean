/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.BooleanRetrieval
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Multiset.Basic

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- A term-list collection on documents `Fin N`: each document is a list of
terms, keeping order and repetition. A token's position is its list index. -/
abbrev TermListCollection (N : ℕ) (α : Type*) := Fin N → List α

/-- View each term list as a multiset. Only Boolean membership semantics
agree with the term lists; order is forgotten. -/
def TermListCollection.toCorpus {N : ℕ} {α : Type*}
    (D : TermListCollection N α) : Corpus N α :=
  fun d => (D d : Multiset α)

/-- Term `t` occurs in document `d`: `t` is a member of the term list. -/
def TermListCollection.occurs {N : ℕ} {α : Type*}
    (D : TermListCollection N α) (t : α) (d : Fin N) : Prop :=
  t ∈ D d

/-- Occurrence is decidable via list membership. -/
instance TermListCollection.decidableOccurs {N : ℕ} {α : Type*} [DecidableEq α]
    (D : TermListCollection N α) (t : α) : DecidablePred (D.occurs t) :=
  fun d => inferInstanceAs (Decidable (t ∈ D d))

/-- Occurrence unfolds to membership at some list position. -/
theorem TermListCollection.occurs_iff_exists_position {N : ℕ} {α : Type*}
    (D : TermListCollection N α) (t : α) (d : Fin N) :
    D.occurs t d ↔ ∃ p : ℕ, (D d)[p]? = some t := by
  exact List.mem_iff_getElem?

/-- `docsWith` on the multiset view selects documents by `occurs`. -/
theorem TermListCollection.docsWith_toCorpus {N : ℕ} {α : Type*} [DecidableEq α]
    (D : TermListCollection N α) (t : α) :
    docsWith D.toCorpus t = Finset.univ.filter (fun d => D.occurs t d) := by
  ext d
  simp only [docsWith, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

/-- Term-list satisfaction of a Boolean query by a document. -/
def TermListCollection.Satisfies {N : ℕ} {α : Type*} (D : TermListCollection N α) :
    BoolQuery α → Fin N → Prop
  | BoolQuery.term t, d => D.occurs t d
  | BoolQuery.and q1 q2, d => D.Satisfies q1 d ∧ D.Satisfies q2 d
  | BoolQuery.or q1 q2, d => D.Satisfies q1 d ∨ D.Satisfies q2 d
  | BoolQuery.not q, d => ¬ D.Satisfies q d

/-- Query evaluation on the multiset view agrees with term-list satisfaction. -/
theorem TermListCollection.mem_evalSet_toCorpus_iff {N : ℕ} {α : Type*}
    [DecidableEq α] (D : TermListCollection N α) (q : BoolQuery α) (d : Fin N) :
    d ∈ q.evalSet D.toCorpus ↔ D.Satisfies q d := by
  induction q with
  | term t =>
      simp [BoolQuery.evalSet, docsWith, TermListCollection.toCorpus,
        TermListCollection.occurs, TermListCollection.Satisfies, Multiset.mem_coe]
  | and q1 q2 ih1 ih2 =>
      simp [BoolQuery.evalSet, TermListCollection.Satisfies, ih1, ih2]
  | or q1 q2 ih1 ih2 =>
      simp [BoolQuery.evalSet, TermListCollection.Satisfies, ih1, ih2]
  | not q ih =>
      simp [BoolQuery.evalSet, TermListCollection.Satisfies, ih]

end Cslib.InformationRetrieval
