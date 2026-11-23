/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.BooleanRetrieval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for Boolean retrieval and inverted indexes
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.BooleanRetrieval

/-- A three-document corpus over natural-number terms. Document `0` contains
term `0` twice and term `1` once; document `1` contains term `1`; document
`2` is empty. -/
def corpus3 : Corpus 3 ℕ :=
  ![↑[0, 0, 1], ↑[1], 0]

/-- Term `0` occurs only in document `0`, despite the duplicate occurrence. -/
example : postings corpus3 0 = [0] := by
  decide

/-- Term `1` occurs in documents `0` and `1`, in increasing order. -/
example : postings corpus3 1 = [0, 1] := by
  decide

/-- An absent term has empty postings. -/
example : postings corpus3 2 = [] := by
  decide

/-- AND evaluation on the concrete corpus. -/
example :
    (BoolQuery.and (BoolQuery.term 0) (BoolQuery.term 1)).evalSet corpus3 = {0} := by
  decide

/-- OR evaluation through the built index on the concrete corpus. -/
example :
    (BoolQuery.or (BoolQuery.term 0) (BoolQuery.term 2)).evalIndex
        (buildIndex corpus3) = {0} := by
  decide

/-- NOT is complement relative to all three documents. -/
example :
    (BoolQuery.not (BoolQuery.term 1)).evalIndex (buildIndex corpus3) = {2} := by
  decide

/-- The main index-correctness theorem, as an example. -/
example {N : ℕ} {α : Type*} [DecidableEq α] (corpus : Corpus N α)
    (q : BoolQuery α) :
    q.evalIndex (buildIndex corpus) = q.evalSet corpus :=
  evalIndex_buildIndex_eq_evalSet corpus q

/-- The postings length/cardinality characterization, as an example. -/
example {N : ℕ} {α : Type*} [DecidableEq α] (corpus : Corpus N α) (t : α) :
    (postings corpus t).length = (docsWith corpus t).card :=
  postings_length_eq_card corpus t

end CSLibExtTest.InformationRetrieval.BooleanRetrieval
