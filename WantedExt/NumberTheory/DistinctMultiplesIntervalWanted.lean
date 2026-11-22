/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distinct multiples of `1, …, n` in an interval

Statements from Wouter van Doorn, *On the Length of an Interval That Contains Distinct
Multiples of the First n Positive Integers*, INTEGERS 26 (2026), Article A7.

Following Erdős and Pomerance, `f(n, m)` is the least `L` such that the interval
`(m, m + L]` contains distinct integers `a₁, …, aₙ` with `i ∣ aᵢ` for every `i`. It is
`distinctMultiplesIntervalLength` from `MathlibExt.NumberTheory.DistinctMultiplesInterval`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.NumberTheory.DistinctMultiplesInterval

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 2: for all positive integers `k` and `n`,
`kn + f(kn, kn) ≤ k²n + f(n, k²n)`.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Lemma 2
(`integers-2026-A7-lem-2`). -/
public theorem_wanted distinctMultiplesIntervalLength_mul_le {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) :
    k * n + distinctMultiplesIntervalLength (k * n) (k * n) ≤
      k ^ 2 * n + distinctMultiplesIntervalLength n (k ^ 2 * n)

/-- Lemma 3 (Erdős and Pomerance): for every `ε > 0` and all large enough `n`,
`(2/√e - ε) n √(log n / log log n) < f(n, n) < (2 + ε) n √(log n)`, the paper's
`(2/√e + o(1)) n √(log n / log log n) < f(n, n) < (2 + o(1)) n √(log n)`.  The record's
constants are garbled; they are read from the paper text (arXiv:2601.16972, same paper,
Lemma 3), consistent with the record's `√2e > 1.21` remark (`2/√e ≈ 1.213`).

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Lemma 3
(`integers-2026-A7-lem-3`), quoting Erdős and Pomerance. -/
public theorem_wanted distinctMultiplesIntervalLength_diag_bounds (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 / Real.sqrt (Real.exp 1) - ε) * n * Real.sqrt (Real.log n / Real.log (Real.log n)) <
          distinctMultiplesIntervalLength n n ∧
        (distinctMultiplesIntervalLength n n : ℝ) < (2 + ε) * n * Real.sqrt (Real.log n)

/-- Theorem 1: for all large enough `n` there is a positive `m` with
`f(n, m) - f(n, n) > 0.36 n log n / log log n`; equivalently
`max_m f(n, m) - f(n, n) > 0.36 n log n / log log n`.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Theorem 1
(`integers-2026-A7-thm-1`). -/
public theorem_wanted exists_distinctMultiplesIntervalLength_sub_gt :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℕ, 0 < m ∧
      0.36 * (n : ℝ) * Real.log n / Real.log (Real.log n) <
        (distinctMultiplesIntervalLength n m : ℝ) - distinctMultiplesIntervalLength n n

end

end MetaMathlibExt
