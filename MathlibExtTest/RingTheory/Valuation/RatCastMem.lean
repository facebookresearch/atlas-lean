/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.RatCastMem

/-! # Consumers for `ValuationSubring.ratCast_mem_iff_padicValRat_nonneg` -/

namespace ValuationSubringRatCastMemTest

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : (r : K) ∈ A ↔ 0 ≤ padicValRat q r :=
  A.ratCast_mem_iff_padicValRat_nonneg hq hA hr

/-- Boundary: `1 / 2` has negative `2`-adic valuation, so the right-hand side
fails; the nonzero hypothesis excludes the degenerate rational `0`. -/
public example : ¬(0 ≤ padicValRat 2 (1 / 2 : ℚ)) := by
  norm_num [padicValRat_def]

/-- At `r = 1` both sides are as expected: the valuation is `0`. -/
public example : padicValRat 2 (1 : ℚ) = 0 := by norm_num [padicValRat_def]

end ValuationSubringRatCastMemTest
