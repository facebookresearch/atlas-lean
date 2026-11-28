/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.AbsoluteMaximalSetsOfLanes
public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSinglesLimits
public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableStrictGrowth
public import MathlibExt.Combinatorics.Enumerative.LonelySinglesLowerBound
public import MathlibExt.Combinatorics.Enumerative.RestrictedMaximalSetsOfLanes

/-!
# Lonely singles and marriageable singles partitions (statements)

Statement-only targets from Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to
Crossroads and Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1.

Noncrossing partitions of `[n]` are `NoncrossingPartition n` (partitions of `Fin n`). A
noncrossing partition is a *marriageable singles* partition if two of its singleton blocks can be
merged with the result still noncrossing, and a *lonely singles* partition otherwise; `M_n` and
`L_n` count them.

For the road-intersection statements, a standard road intersection of size `n` has entries
`E_1, …, E_n` and exits `X_1, …, X_n` alternating clockwise on a circle; the lane `E_iX_j` is the
pair `(i, j) : Fin n × Fin n`, and its endpoints sit at the circle positions `2i` (entry) and
`2j + 1` (exit) (zero-based).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Counting noncrossing partitions with no or one singleton block.** Write $NC_{n,m,k}$ for the
number of noncrossing partitions of $\{0, \dots, n-1\}$ with $m$ blocks of which $k$ are
singletons, and extend the binomial coefficient $\binom{a}{b}$ to all integers $a$, $b$ by setting
it to $0$ when $a < 0$ or $b < 0$. For all natural numbers $n$ and $m$: if $(n, m) \ne (0, 0)$,
then the following holds in $\mathbb{Q}$, where $1/0$ is taken to be $0$ (the denominator
vanishes only for $m = n + 1$, where $\binom{n}{m} = 0$):
$$NC_{n,m,0} = \frac{1}{n-m+1} \binom{n}{m} \binom{n-m-1}{m-1};$$
and if $(n, m) \ne (1, 1)$, then
$$NC_{n,m,1} = \binom{n}{m-1} \binom{n-m-1}{m-2}.$$

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 24
(`jis-2025-25.1.1-prop-24`). -/
public theorem_wanted noncrossingBlockSingletonCount_formulas (n m : ℕ) :
    ((n, m) ≠ (0, 0) →
      (noncrossingBlockSingletonCount n m 0 : ℚ) =
        1 / ((n : ℚ) - m + 1) * zeroExtendedChoose n m *
          zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 1)) ∧
    ((n, m) ≠ (1, 1) →
      noncrossingBlockSingletonCount n m 1 =
        zeroExtendedChoose n ((m : ℤ) - 1) * zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 2))

/-- **Lower bound for the number of marriageable singles partitions.** Extend the binomial
coefficient $\binom{a}{b}$ to all integers $a$, $b$ by setting it to $0$ when $a < 0$ or $b < 0$,
and for every natural number $N$ let
$$S(N) = \sum_{m=0}^{\lfloor N/2 \rfloor} \frac{1}{N-m+1} \binom{N}{m} \binom{N-m-1}{m-1}.$$
For every $n \ge 3$, the number $M_n$ of noncrossing partitions of $\{0, \dots, n-1\}$ that are
marriageable singles partitions satisfies
$$M_n \ge \sum_{i=1}^{n-1} \sum_{j=i+1}^{n} S(n+i-j-1)\, S(j-i-1).$$

For $N \ge 1$, $S(N)$ is the number of noncrossing partitions of an $N$-element set with no
singleton block; with the convention above, $S(0) = 0$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 27
(`jis-2025-25.1.1-prop-27`). -/
public theorem_wanted marriageableSinglesCount_ge_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ Finset.Icc 1 (n - 1), ∑ j ∈ Finset.Icc (i + 1) n,
      (∑ m ∈ Finset.range ((n + i - j - 1) / 2 + 1),
          1 / ((n : ℚ) + i - j - m) * zeroExtendedChoose ((n : ℤ) + i - j - 1) m *
            zeroExtendedChoose ((n : ℤ) + i - j - m - 2) ((m : ℤ) - 1)) *
        (∑ m ∈ Finset.range ((j - i - 1) / 2 + 1),
          1 / ((j : ℚ) - i - m) * zeroExtendedChoose ((j : ℤ) - i - 1) m *
            zeroExtendedChoose ((j : ℤ) - i - m - 2) ((m : ℤ) - 1))) ≤
      marriageableSinglesCount n

end

end MetaMathlibExt
