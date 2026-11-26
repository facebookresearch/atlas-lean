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
public import MathlibExt.NumberTheory.DistinctMultiplesIntervalMul
public import MathlibExt.NumberTheory.DistinctMultiplesIntervalShift

namespace MetaMathlibExt

@[expose] public section

/-- **Erdős–Pomerance bounds for the diagonal interval length.** For natural numbers $n$ and $m$,
let $f(n, m)$ be the least natural number $L$ such that the interval $(m, m + L]$ contains
distinct multiples of $1, \dots, n$. For every real $\varepsilon > 0$ and all sufficiently large
natural numbers $n$,
$$
\left(\frac{2}{\sqrt{e}} - \varepsilon\right) n \sqrt{\frac{\log n}{\log \log n}} < f(n, n) <
(2 + \varepsilon)\, n \sqrt{\log n}.
$$

Source: the constants are read from the paper text (arXiv:2601.16972, same paper, Lemma 3),
since the record's are garbled; they agree with the record's `√2e > 1.21` remark
(`2/√e ≈ 1.213`).

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Lemma 3
(`integers-2026-A7-lem-3`), quoting Erdős and Pomerance. -/
public theorem_wanted distinctMultiplesIntervalLength_diag_bounds (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 / Real.sqrt (Real.exp 1) - ε) * n * Real.sqrt (Real.log n / Real.log (Real.log n)) <
          distinctMultiplesIntervalLength n n ∧
        (distinctMultiplesIntervalLength n n : ℝ) < (2 + ε) * n * Real.sqrt (Real.log n)

end

end MetaMathlibExt
