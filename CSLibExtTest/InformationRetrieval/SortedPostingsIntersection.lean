/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.InformationRetrieval.SortedPostingsIntersection
import Mathlib.Data.Fin.VecNotation

/-! # Tests for sorted postings intersection -/

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.SortedPostingsIntersection

example : intersectPostings ([] : List ℕ) [] = ⟨[], 0⟩ := by cbv

example : intersectPostings [] [2, 4] = ⟨[], 0⟩ := by cbv

example : intersectPostings [2, 4] [] = ⟨[], 0⟩ := by cbv

example : intersectPostings [4] [4] = ⟨[4], 1⟩ := by
  cbv

-- Alternating disjoint lists exhaust the left side after 3 + 3 - 1 comparisons.
example : intersectPostings [1, 3, 5] [2, 4, 6] = ⟨[], 5⟩ := by
  cbv

-- Equal lengths and the same empty output do not determine the cost.
example : intersectPostings [1, 2, 3] [4, 5, 6] = ⟨[], 3⟩ := by
  cbv

-- Drop from the left, drop from the right, and emit two common heads.
example : intersectPostings [1, 4, 6, 7] [2, 4, 5, 7] = ⟨[4, 7], 6⟩ := by
  cbv

-- Repeating a term within a document does not repeat the document in the answer.
private def corpus : Corpus 4 ℕ := ![↑[3, 3], ↑[3, 5, 5], ↑[5], ↑[3, 3, 5]]

example : intersectPostings (buildIndex corpus 3) (buildIndex corpus 5) = ⟨[1, 3], 4⟩ := by
  cbv

example (d : Fin 4) :
    d ∈ (intersectPostings (buildIndex corpus 3) (buildIndex corpus 5)).ret ↔
      3 ∈ corpus d ∧ 5 ∈ corpus d := by
  simpa [docsWith] using mem_intersectPostings_buildIndex corpus 3 5 d

end CSLibExtTest.InformationRetrieval.SortedPostingsIntersection
