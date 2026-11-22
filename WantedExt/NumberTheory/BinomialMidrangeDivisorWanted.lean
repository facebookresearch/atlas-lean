/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic

/-!
# Mid-sized divisors of binomial coefficients

Erdős Problem 387 asks for an absolute positive constant `c` such that every
nontrivial binomial coefficient `n.choose k` has a divisor `d` in the interval
`(c n, n]`.
-/

namespace MathlibExt.NumberTheory.BinomialMidrangeDivisorWanted

/-- Erdős Problem 387: every nontrivial binomial coefficient has a divisor
whose size is bounded below by a fixed positive proportion of `n`. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, d ∣ n.choose k ∧ c * (n : ℝ) < (d : ℝ) ∧ d ≤ n

/--
Resolved false: Bui, Naprienko, Pratt and Zaharescu (arXiv:2605.21221, 2026), Theorem 1.4: for
arbitrarily large k there are infinitely many n such that C(n,k) has no divisor in (n*241 log
log k/log k, n], so no fixed c>0 works and the Lean existential is false. Source: H. M. Bui, S.
Naprienko, K. Pratt, A. Zaharescu, Binomial coefficients with divisors avoiding an interval,
arXiv preprint (2026), arXiv:2605.21221, https://arxiv.org/abs/2605.21221. Moved from
`OpenConjectures/NumberTheory/BinomialMidrangeDivisor`.
-/
theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.BinomialMidrangeDivisorWanted
