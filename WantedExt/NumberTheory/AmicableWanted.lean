/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalizations of amicable numbers

Statements from Stoyan Dimitrov, "Generalizations of
Amicable Numbers", *Journal of Integer Sequences* 28
(2025), Article 25.4.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Dimitrov/dimitrov16.html>).

Only Lemmas 1 and 2 are stated. Lemma 3 is not:
the extracted `σ^k(n)` admits two readings, the `k`-th
power `(σ n)^k` (consistent with the extracted proof's
`k`-fold divisor expansion, but then the stated bound
`(ζ 2)^k * ζ (2k-1) * x` is numerically false, e.g. at
`k = 3`, `x = 24` the sum is `≈ 116.9 > 110.8`) and the
divisor power-sum `∑_{d ∣ n} d^k` (consistent with the
bound, inconsistent with the proof expansion); which is
intended cannot be settled from the extraction.
Theorems 4 and 5 are not stated either: they are about
the paper's `(α₁, …, α_k)`-multiamicable tuples, whose
definition is not in the extracted statements. See the
source audit table. Here `σ n` is `∑ d ∈ n.divisors, d`
and `ζ` values at integers `> 1` are written as the
defining series `∑' n, 1 / (n + 1) ^ s`. Lemma 2 was
verified numerically for `x ≤ 600`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.Data.Set.Density

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.AmicableWanted

/-- **A fixed positive integer divides the divisor sum of almost every natural number.** For
a natural number $l$ let $\sigma(l)$ denote the sum of the positive divisors of $l$, with
$\sigma(0) = 0$. Then for every positive integer $N$, the set of natural numbers $l$ such
that $N$ does not divide $\sigma(l)$ has natural density $0$.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 1. -/
theorem_wanted tendsto_density_not_dvd_sigma (N : ℕ)
    (hN : 1 ≤ N) :
    {l : ℕ | ¬ N ∣ ArithmeticFunction.sigma 1 l}.HasDensity 0

/-- **Linear bound for the partial sums of the abundancy index.** For a positive integer
$n$ let $\sigma(n)$ denote the sum of the positive divisors of $n$, and let
$\zeta(2) = \sum_{n=1}^{\infty} 1/n^2$. Then for every real number $x \ge 1$,
$$\sum_{n=1}^{\lfloor x \rfloor} \frac{\sigma(n)}{n} < \zeta(2)\, x.$$

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 2. -/
theorem_wanted sum_sigma_div_lt (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.sigma 1 n : ℝ) / n <
      (∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2) * x

end MathlibExt.NumberTheory.AmicableWanted
