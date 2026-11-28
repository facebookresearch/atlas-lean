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
public import MathlibExt.NumberTheory.DivisibilityRunsDivRunCountThree
public import MathlibExt.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds
public import MathlibExt.NumberTheory.DivisibilityRunsNoInfiniteRun

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
