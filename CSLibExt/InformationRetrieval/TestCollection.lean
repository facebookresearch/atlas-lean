/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.PrecisionAt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

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

/-- Cranfield-style test collection: partial binary relevance judgments. -/
structure TestCollection (N : ℕ) (Q : Type*) where
  /-- `some true` relevant, `some false` nonrelevant, `none` unjudged. -/
  qrels : Q → Fin N → Option Bool

/-- Relevance predicate used by `precisionAt`: judged relevant. -/
def TestCollection.relevant {N : ℕ} {Q : Type*} (T : TestCollection N Q)
    (q : Q) : Fin N → Prop :=
  fun d => T.qrels q d = some true

instance TestCollection.decidableRelevant {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) :
    DecidablePred (T.relevant q) :=
  fun d => decEq (T.qrels q d) (some true)

/-- Membership in `relevant` unfolds to a `some true` judgment. -/
theorem TestCollection.relevant_iff {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N) :
    T.relevant q d ↔ T.qrels q d = some true :=
  Iff.rfl

/-- Unjudged documents are nonrelevant. -/
theorem TestCollection.not_relevant_of_unjudged {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N)
    (h : T.qrels q d = none) : ¬ T.relevant q d := by
  rw [TestCollection.relevant_iff, h]
  simp

/-- Documents judged nonrelevant are nonrelevant. -/
theorem TestCollection.not_relevant_of_judged_nonrelevant {N : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (d : Fin N)
    (h : T.qrels q d = some false) :
    ¬ T.relevant q d := by
  rw [TestCollection.relevant_iff, h]
  simp

/-- Precision at a cutoff over `relevant` lies in `[0, 1]`. -/
theorem TestCollection.precisionAt_relevant_mem_Icc {N k : ℕ} {Q : Type*}
    (T : TestCollection N Q) (q : Q) (r : Fin k → Fin N) :
    precisionAt (T.relevant q) r ∈ Set.Icc (0 : ℝ) 1 :=
  precisionAt_mem_Icc (T.relevant q) r

end Cslib.InformationRetrieval
