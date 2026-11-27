/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.InformationRetrieval.TermListCollection

/-!
# Tests for term-list document collections
-/

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- Fixture over `Fin 3`: doc 0 = `[0, 1, 0]`, doc 1 = `[1, 2]`, doc 2 = `[]`. -/
def testDocs : TermListCollection 3 ℕ
  | ⟨0, _⟩ => [0, 1, 0]
  | ⟨1, _⟩ => [1, 2]
  | _ => []

-- T1: `occurs` and `docsWith` on `toCorpus` for terms 0, 1, 2.
example : docsWith testDocs.toCorpus 0 = {0} := by
  rw [TermListCollection.docsWith_toCorpus]
  decide
example : docsWith testDocs.toCorpus 1 = {0, 1} := by
  rw [TermListCollection.docsWith_toCorpus]
  decide
example : docsWith testDocs.toCorpus 2 = {1} := by
  rw [TermListCollection.docsWith_toCorpus]
  decide
example : testDocs.occurs 0 0 := by decide
example : ¬ testDocs.occurs 2 0 := by decide

-- T2: term 0 occurs in doc 0 at positions 0 and 2.
example : (testDocs 0)[0]? = some 0 ∧ (testDocs 0)[2]? = some 0 := ⟨rfl, rfl⟩
example : testDocs.occurs 0 0 :=
  (TermListCollection.occurs_iff_exists_position testDocs 0 0).mpr ⟨0, rfl⟩

-- T3: the NOT-only query over term 0 selects docs 1 and 2.
example : (BoolQuery.not (BoolQuery.term 0)).evalSet testDocs.toCorpus = {1, 2} := by
  decide

/-- Test query: `1 AND (0 OR 2)`. -/
def testQuery : BoolQuery ℕ :=
  BoolQuery.and (BoolQuery.term 1)
    (BoolQuery.or (BoolQuery.term 0) (BoolQuery.term 2))

-- T4: `evalSet` and `Satisfies` agree on all three documents.
example (d : Fin 3) :
    d ∈ testQuery.evalSet testDocs.toCorpus ↔ testDocs.Satisfies testQuery d :=
  TermListCollection.mem_evalSet_toCorpus_iff testDocs testQuery d
example : testQuery.evalSet testDocs.toCorpus = {0, 1} := by decide

-- T5: `toCorpus` forgets order.
/-- One-document fixture with term list `[0, 1]`. -/
def oneDocA : TermListCollection 1 ℕ := fun _ => [0, 1]
/-- The terms of `oneDocA` in the reverse order, `[1, 0]`. -/
def oneDocB : TermListCollection 1 ℕ := fun _ => [1, 0]
example : oneDocA.toCorpus = oneDocB.toCorpus := by decide

end Cslib.InformationRetrieval
