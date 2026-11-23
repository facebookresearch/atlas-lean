/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Boolean retrieval and inverted indexes

For a finite corpus on documents `Fin N`, each document is a multiset of
terms and Boolean retrieval depends only on term membership. The postings
for a term are the increasing list of documents containing it. Evaluating a
Boolean query from the built index agrees with direct set semantics, where
negation is complement relative to the full document universe.

The cardinality bounds below are linear output-size bounds for union,
intersection, and difference of duplicate-free postings lists. They are not a
TimeM runtime theorem and make no relevance-quality claim.

## Main declarations

* `Corpus`: a finite corpus of term multisets.
* `BoolQuery.evalSet`: direct set-semantics query evaluation.
* `postings`, `buildIndex`: sorted postings and the inverted index.
* `BoolQuery.evalIndex`: query evaluation from postings lists.
* `evalIndex_buildIndex_eq_evalSet`: index evaluation agrees with set semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- A finite corpus on documents `Fin N`: each document is a multiset of terms.
Only term membership matters for Boolean retrieval. -/
abbrev Corpus (N : ℕ) (α : Type*) := Fin N → Multiset α

/-- Boolean queries over terms. Negation is always relative to the finite
document universe in the semantics below. -/
inductive BoolQuery (α : Type*) where
  | term (t : α)
  | and (q₁ q₂ : BoolQuery α)
  | or (q₁ q₂ : BoolQuery α)
  | not (q : BoolQuery α)

/-- Documents containing term `t`, as a finset. -/
def docsWith {N : ℕ} {α : Type*} [DecidableEq α] (corpus : Corpus N α)
    (t : α) : Finset (Fin N) :=
  Finset.univ.filter fun d => t ∈ corpus d

/-- Set-semantics evaluation of a Boolean query. `not q` is complement
relative to all documents `Finset.univ`. -/
def BoolQuery.evalSet {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) : BoolQuery α → Finset (Fin N)
  | term t => docsWith corpus t
  | and q₁ q₂ => evalSet corpus q₁ ∩ evalSet corpus q₂
  | or q₁ q₂ => evalSet corpus q₁ ∪ evalSet corpus q₂
  | not q => Finset.univ \ evalSet corpus q

/-- Sorted postings for term `t`: documents containing `t`, in increasing
document order. -/
def postings {N : ℕ} {α : Type*} [DecidableEq α] (corpus : Corpus N α)
    (t : α) : List (Fin N) :=
  (List.finRange N).filter fun d => decide (t ∈ corpus d)

/-- The inverted index: sorted postings for every term. -/
def buildIndex {N : ℕ} {α : Type*} [DecidableEq α] (corpus : Corpus N α) :
    α → List (Fin N) :=
  fun t => postings corpus t

/-- Evaluation of a Boolean query from postings lists. Term postings are read
as finsets, then combined by intersection, union, and difference from the
document universe. -/
def BoolQuery.evalIndex {N : ℕ} {α : Type*} (index : α → List (Fin N)) :
    BoolQuery α → Finset (Fin N)
  | term t => (index t).toFinset
  | and q₁ q₂ => evalIndex index q₁ ∩ evalIndex index q₂
  | or q₁ q₂ => evalIndex index q₁ ∪ evalIndex index q₂
  | not q => Finset.univ \ evalIndex index q

/-- Postings are strictly increasing. -/
theorem postings_pairwise_lt {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) (t : α) :
    List.Pairwise (· < ·) (postings corpus t) := by
  unfold postings
  exact List.Pairwise.filter _ (List.pairwise_lt_finRange N)

/-- Postings have no duplicate documents. -/
theorem postings_nodup {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) (t : α) :
    (postings corpus t).Nodup := by
  unfold postings
  exact (List.nodup_finRange N).filter _

/-- The postings list for a term denotes exactly the documents containing it. -/
theorem postings_toFinset {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) (t : α) :
    (postings corpus t).toFinset = docsWith corpus t := by
  ext d
  simp [postings, docsWith]

/-- The postings length is the number of documents containing the term. -/
theorem postings_length_eq_card {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) (t : α) :
    (postings corpus t).length = (docsWith corpus t).card := by
  have h := postings_toFinset corpus t
  have hn := postings_nodup corpus t
  rw [← h]
  exact (List.toFinset_card_of_nodup hn).symm

/-- Evaluating a query through the built inverted index gives the
set-semantics answer. -/
theorem evalIndex_buildIndex_eq_evalSet {N : ℕ} {α : Type*} [DecidableEq α]
    (corpus : Corpus N α) (q : BoolQuery α) :
    q.evalIndex (buildIndex corpus) = q.evalSet corpus := by
  induction q with
  | term t => exact postings_toFinset corpus t
  | and _ _ ih₁ ih₂ =>
    simp [BoolQuery.evalIndex, BoolQuery.evalSet, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp [BoolQuery.evalIndex, BoolQuery.evalSet, ih₁, ih₂]
  | not _ ih => simp [BoolQuery.evalIndex, BoolQuery.evalSet, ih]

/-- Linear size bound for a union of two postings lists. -/
theorem card_postings_union_le {N : ℕ} {xs ys : List (Fin N)}
    (hx : xs.Nodup) (hy : ys.Nodup) :
    (xs.toFinset ∪ ys.toFinset).card ≤ xs.length + ys.length := by
  have h := Finset.card_union_le xs.toFinset ys.toFinset
  rwa [List.toFinset_card_of_nodup hx, List.toFinset_card_of_nodup hy] at h

/-- Linear size bound for an intersection of two postings lists. -/
theorem card_postings_inter_le {N : ℕ} {xs ys : List (Fin N)}
    (hx : xs.Nodup) (_hy : ys.Nodup) :
    (xs.toFinset ∩ ys.toFinset).card ≤ xs.length + ys.length := by
  have hsub : xs.toFinset ∩ ys.toFinset ⊆ xs.toFinset := Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hx] at hcard
  omega

/-- Linear size bound for a difference of two postings lists. -/
theorem card_postings_diff_le {N : ℕ} {xs ys : List (Fin N)}
    (hx : xs.Nodup) (_hy : ys.Nodup) :
    (xs.toFinset \ ys.toFinset).card ≤ xs.length + ys.length := by
  have hsub : xs.toFinset \ ys.toFinset ⊆ xs.toFinset := Finset.sdiff_subset
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hx] at hcard
  omega

end Cslib.InformationRetrieval
