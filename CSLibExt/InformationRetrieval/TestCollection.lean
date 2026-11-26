/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.PrecisionAt

/-!
# Test collections for ad hoc retrieval evaluation

A test collection bundles a document universe with topics and relevance
judgments, following Manning, Raghavan and Schütze, *Introduction to
Information Retrieval* (2008): §8.1 (document collection, information needs
as queries, binary relevance judgments), §8.2 (needs called topics; judgments
available only for pooled top-ranked documents) and §8.5 (pooling over a
subset of the collection).

Judgments are binary and partial: `some true` is judged relevant, `some false`
is judged nonrelevant, and `none` is unjudged. As a convention of the model in
this module, a document with no judgment for a topic is treated as nonrelevant
for that topic.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- **Test collection.** A Cranfield-style test collection: partial binary
relevance judgments. -/
structure TestCollection (N : ℕ) (Q : Type*) where
  /-- `some true` relevant, `some false` nonrelevant, `none` unjudged. -/
  qrels : Q → Fin N → Option Bool

/-- **Judged-relevant predicate.** The relevance predicate used by
`precisionAt`: a document counts as relevant to a topic only when it is judged
relevant. -/
def TestCollection.relevant {N : ℕ} {Q : Type*} (T : TestCollection N Q)
    (q : Q) : Fin N → Prop :=
  fun d => T.qrels q d = some true

instance TestCollection.decidableRelevant {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) :
    DecidablePred (T.relevant q) :=
  fun d => decEq (T.qrels q d) (some true)

/-- **Relevant means judged relevant.** Membership in `relevant` unfolds to a
`some true` judgment. -/
theorem TestCollection.relevant_iff {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N) :
    T.relevant q d ↔ T.qrels q d = some true :=
  Iff.rfl

/-- **Unjudged documents are not judged relevant.** Unjudged documents do not
count as relevant under this precision convention. -/
theorem TestCollection.not_relevant_of_unjudged {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N)
    (h : T.qrels q d = none) : ¬ T.relevant q d := by
  rw [TestCollection.relevant_iff, h]
  simp

/-- **Judged-nonrelevant documents are not judged relevant.** Documents judged
nonrelevant do not count as relevant. -/
theorem TestCollection.not_relevant_of_judged_nonrelevant {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N)
    (h : T.qrels q d = some false) :
    ¬ T.relevant q d := by
  rw [TestCollection.relevant_iff, h]
  simp

end Cslib.InformationRetrieval
