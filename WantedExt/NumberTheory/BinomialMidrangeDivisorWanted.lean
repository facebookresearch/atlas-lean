/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Mid-sized divisors of binomial coefficients

Erdős Problem 387 asks for an absolute positive constant `c` such that every
nontrivial binomial coefficient `n.choose k` has a divisor `d` in the interval
`(c n, n]`.
-/

namespace MathlibExt.NumberTheory.BinomialMidrangeDivisorWanted

/-- **Erdős Problem 387.** The proposition that there is a real number $c > 0$ such that for all
natural numbers $n$ and $k$ with $1 \le k < n$, the binomial coefficient $\binom{n}{k}$ has a
divisor $d$ with $cn < d \le n$. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, d ∣ n.choose k ∧ c * (n : ℝ) < (d : ℝ) ∧ d ≤ n

/--
**Erdős Problem 387 is false.** There is no real number $c > 0$ such that for all natural
numbers $n$ and $k$ with $1 \le k < n$ the binomial coefficient $\binom{n}{k}$ has a divisor
$d$ with $cn < d \le n$.

This follows from Theorem 1.4 of Bui, Naprienko, Pratt and Zaharescu: for arbitrarily large
$k$ there are infinitely many $n$ such that $\binom{n}{k}$ has no divisor in the interval
$(241\, n \log\log k / \log k,\ n]$.

Source: H. M. Bui, S.
Naprienko, K. Pratt, A. Zaharescu, Binomial coefficients with divisors avoiding an interval,
arXiv preprint (2026), arXiv:2605.21221, https://arxiv.org/abs/2605.21221. Moved from
`OpenConjectures/NumberTheory/BinomialMidrangeDivisor`.
-/
theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.BinomialMidrangeDivisorWanted
