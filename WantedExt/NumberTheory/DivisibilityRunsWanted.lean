/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.DivRunCountFour
public import MathlibExt.NumberTheory.DivRunCountOne
public import MathlibExt.NumberTheory.DivisibilityRuns
public import MathlibExt.NumberTheory.GeneralizedTribonacciBasis
public import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib
public import MathlibExt.NumberTheory.DivisibilityRunsDivRunCountTwo
public import MathlibExt.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds

namespace MetaMathlibExt

@[expose] public section

/-- **Divisibility by a Gibonacci sequence forces a Tribonacci sequence to vanish.** Let
$x, y, a, b, c$ be integers, let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and
$P_1 = y$, and let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci sequence with $Q_0 = a$,
$Q_1 = b$ and $Q_2 = c$. If $P_n \ne 0$ and $P_n \mid Q_n$ for every $n \ge 0$, then $Q_n = 0$
for every $n \ge 0$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 1
(`integers-2026-A122-thm-1`). -/
public theorem_wanted generalizedTribonacci_eq_zero_of_dvd (x y a b c : ℤ)
    (hP : ∀ n : ℕ, gibonacciNumber x y n ≠ 0)
    (hdiv : ∀ n : ℕ, gibonacciNumber x y n ∣ generalizedTribonacci a b c n) :
    ∀ n : ℕ, generalizedTribonacci a b c n = 0


/-- **Divisibility runs have logarithmic length.** There is a real constant $C > 0$ such that for
every natural number $B \ge 2$, all integers $x, y, a, b, c \in [-B, B]$ with $(x, y) \ne (0, 0)$
and $(a, b, c) \ne (0, 0, 0)$, and every natural number $L$ such that $(x, y, a, b, c)$ has a
divisibility run of length at least $L$, we have $L \le C \log B$. Here a divisibility run of
length at least $L$ means that for every $i < L$ the Gibonacci number $P_i$ with $P_0 = x$,
$P_1 = y$ is nonzero and divides the generalized Tribonacci number $Q_i$ with $Q_0 = a$,
$Q_1 = b$, $Q_2 = c$.

In the paper's notation this is $E(B) \le C \log B$, where $E(B)$ is the maximal run length
over these configurations.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 2
(`integers-2026-A122-thm-2`). -/
public theorem_wanted divRun_length_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B → ∀ x y a b c : ℤ,
      x ∈ Set.Icc (-(B : ℤ)) B → y ∈ Set.Icc (-(B : ℤ)) B → a ∈ Set.Icc (-(B : ℤ)) B →
      b ∈ Set.Icc (-(B : ℤ)) B → c ∈ Set.Icc (-(B : ℤ)) B →
      (x, y) ≠ (0, 0) → (a, b, c) ≠ (0, 0, 0) →
      ∀ L : ℕ, IsDivRunUpTo x y a b c L → (L : ℝ) ≤ C * Real.log B

/-- **Asymptotics of the length-one run count.** There is a real constant $K$ such that for every
natural number $B \ge 2$ the number $A_B(1)$ of integer tuples $(x, y, a, b, c) \in [-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $1$ satisfies $|A_B(1) - 32 B^4 \log B| \le K B^4$; that is,
$A_B(1) = 32 B^4 \log B + O(B^4)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem_wanted divRunCount_one_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 1 : ℝ) - 32 * (B : ℝ) ^ 4 * Real.log B| ≤ K * (B : ℝ) ^ 4

/-- **Asymptotics of the length-two run count.** There is a real constant $K$ such that for every
natural number $B \ge 2$ the number $A_B(2)$ of integer tuples $(x, y, a, b, c) \in [-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $2$ satisfies $|A_B(2) - 32 B^3 (\log B)^2| \le K B^3 \log B$; that is,
$A_B(2) = 32 B^3 (\log B)^2 + O(B^3 \log B)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem_wanted divRunCount_two_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 2 : ℝ) - 32 * (B : ℝ) ^ 3 * Real.log B ^ 2|
        ≤ K * (B : ℝ) ^ 3 * Real.log B

/-- **Exact formula for the length-three run count.** For a natural number $B$, let $A_B(3)$ be
the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $3$, and for integers
$m \ge 1$ let $d_B(m) = 2\lfloor B/m \rfloor + 1$. Then
$$A_B(3) = \sum_{x, y} \left(d_B(|x|)\, d_B(|y|)\, d_B(|x+y|) - 1\right),$$
where the sum runs over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$ and
$x + y \ne 0$, and also
$$
A_B(3) = 2 \sum_{m=1}^{B} \sum_{n=1}^{B} d_B(m)\, d_B(n)\, d_B(m+n) +
4 \sum_{1 \le n < m \le B} d_B(m)\, d_B(n)\, d_B(m-n) - (4B^2 - 2B).
$$

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6
(`integers-2026-A122-prop-6`). -/
public theorem_wanted divRunCount_three (B : ℕ) :
    ((divRunCount B 3 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1)
                * (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ)
            else 0) ∧
    (divRunCount B 3 : ℤ)
        = 2 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)
          + 4 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ)
          - (4 * B ^ 2 - 2 * B)

end

end MetaMathlibExt
