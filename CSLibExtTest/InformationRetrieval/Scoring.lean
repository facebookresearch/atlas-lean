/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.Scoring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for BM25 term scoring
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.Scoring

/-- Zero term frequency scores zero, as an example. -/
example (idf k1 b docLen avgLen : ℝ) :
    bm25TermScore idf 0 k1 b docLen avgLen = 0 :=
  bm25TermScore_zero_tf idf k1 b docLen avgLen

/-- At `b = 0` and unit document lengths, the length norm is `1`. -/
example : bm25LengthNorm 0 1 1 = 1 := by
  norm_num [bm25LengthNorm]

/-- With full length normalization (`b = 1`) and a document twice the average
length, the length norm is `2`; the corresponding unit-frequency score is
`2 / 3`, so the `docLen / avgLen` factor is exercised. -/
example : bm25LengthNorm 1 2 1 = 2 ∧ bm25TermScore 1 1 1 1 2 1 = 2 / 3 := by
  constructor <;> norm_num [bm25LengthNorm, bm25TermScore]

/-- With unit parameters and length norm `1`, term frequency `1` scores `1`
and term frequency `3` scores `3 / 2`, below the saturation value `2`. -/
example : bm25TermScore 1 1 1 0 1 1 = 1 ∧ bm25TermScore 1 3 1 0 1 1 = 3 / 2 := by
  constructor <;> norm_num [bm25TermScore, bm25LengthNorm]

/-- The saturation bound instantiated at unit parameters and term frequency `3`. -/
example : 0 ≤ bm25TermScore 1 3 1 0 1 1 ∧ bm25TermScore 1 3 1 0 1 1 ≤ 2 := by
  have hnorm : 0 < bm25LengthNorm 0 1 1 := by
    norm_num [bm25LengthNorm]
  have h := @bm25TermScore_nonneg_le_saturation 1 3 1 0 1 1 (by norm_num)
    (by norm_num) (by norm_num) hnorm
  refine ⟨h.1, ?_⟩
  calc bm25TermScore 1 3 1 0 1 1 ≤ 1 * (1 + 1) := h.2
    _ = 2 := by norm_num

/-- Monotonicity on nonnegative frequencies instantiated at unit parameters. -/
example : bm25TermScore 1 1 1 0 1 1 ≤ bm25TermScore 1 3 1 0 1 1 := by
  have hnorm : 0 < bm25LengthNorm 0 1 1 := by
    norm_num [bm25LengthNorm]
  have hmono := @bm25TermScore_mono_tf 1 1 0 1 1 (by norm_num) (by norm_num) hnorm
  exact hmono (by norm_num) (by norm_num) (by norm_num)

end CSLibExtTest.InformationRetrieval.Scoring
