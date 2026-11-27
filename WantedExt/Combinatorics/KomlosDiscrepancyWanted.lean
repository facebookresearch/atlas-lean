/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.KuniskyKomlosLowerBound
public import MathlibExt.Combinatorics.NikolovVectorColoring
public import MathlibExt.Combinatorics.VectorDiscrepancy
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Batteries.Util.ProofWanted

/-!
# Source requests for the Komlós discrepancy constant

The actual finite matrix and Euclidean vector optimizers are implemented
upstream. These source propositions and private ProofWanted records are not
proofs, assumptions, or claims of verified numerical certificates.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MatrixDiscrepancy

namespace KomlosDiscrepancyWanted

/-- **Beck–Spencer–Gluskin logarithmic upper bound (statement).** The statement that there are a
real number $c > 0$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$,
the Komlós constant in dimension $n$ is at most $c \log n$, where $\log$ is the natural logarithm.

Source: optimization catalogue C24a, line 35, Beck (1981), Spencer (1985), and
Gluskin (1989); their full original theorem texts remain a primary-source gap. -/
def beckSpencerGluskinLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.log n)

/-- **Statement of Banaszczyk's Komlós bound.** The proposition that there are a real constant
$c > 0$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$, the Komlós
constant in dimension $n$ is at most $c \sqrt{\log n}$, where $\log$ is the natural logarithm.

Source: optimization catalogue C24a, line 36, Banaszczyk (1998), also reported
in retained BJ2025 introduction and BDG2019 Theorem `komlos`. -/
def banaszczyk1998SqrtLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.sqrt (Real.log n))

/-- **Statement of the sublogarithmic Komlós bound.** The proposition that for every real
$\varepsilon > 0$ there is a natural number $N \ge 3$ such that for every natural number
$n \ge N$, the Komlós constant in dimension $n$ is at most $\varepsilon \log n$, where $\log$ is
the natural logarithm. In other words, the Komlós constant in dimension $n$ is $o(\log n)$.

Source: optimization catalogue C24a, line 36, the `o(log n)` comment. -/
def banaszczykSublogUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (ε * Real.log n)

/-- **Statement of the Bansal–Dadush–Garg Komlós bound.** The proposition that there are a real
constant $c > 0$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$, the
Komlós constant in dimension $n$ is at most $c \sqrt{\log n}$, where $\log$ is the natural
logarithm.

Only this numerical bound is stated, not the polynomial-time algorithm of the source.

Source: Bansal, Dadush, and Garg, arXiv1605.02882, retained introduction lines
52-60, Theorem `komlos`; efficient randomized/high-probability computation is
an explicit separate gap. -/
def bdg2019NumericalSqrtLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.sqrt (Real.log n))

/-- **Statement of the Bansal–Jiang Komlós bound.** The proposition that there are a real
constant $c > 0$, a natural number $p$ and a natural number $N \ge 3$ such that for every natural
number $n \ge N$, the Komlós constant in dimension $n$ is at most
$c (\log n)^{1/4} (\log \log n)^p$, where $\log$ is the natural logarithm.

Source: Bansal and Haotian Jiang, arXiv2508.03961, retained abstract lines 1-9
and introduction Theorem `thm:Komlos`. The abstract explicitly defines tilde
as `poly(log log n)`; no degree is invented. -/
def bansalJiang2025QuarterLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ p : ℕ, ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal
      (c * (Real.log n) ^ (1 / 4 : ℝ) * (Real.log (Real.log n)) ^ p)

/-- **Statement of the little-o square-root-log Komlós bound.** The proposition that for every
real $\varepsilon > 0$ there is a natural number $N \ge 3$ such that for every natural number
$n \ge N$, the Komlós constant in dimension $n$ is at most $\varepsilon \sqrt{\log n}$, where
$\log$ is the natural logarithm. In other words, the Komlós constant in dimension $n$ is
$o(\sqrt{\log n})$.

Source: optimization catalogue C24a, line 38, and BJ2025's retained abstract. -/
def bansalJiang2025LittleSqrtLogUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (ε * Real.sqrt (Real.log n))

/-- Kunisky's finite lower bound in every dyadic dimension `2 ^ k`.

Source: Kunisky, SIAM J. Discrete Math. 37 (2023), arXiv:2111.02974,
Theorem 1.1. The bound equals `1 + √2 - √2 * 2 ^ (-k / 2)`, so it approaches
`1 + √2` from below; no finite-dimensional attainment of that endpoint is
asserted. -/
def kuniskyInfinitelyManyDimensionsLowerBound : Prop :=
  ∀ k : ℕ,
    ENNReal.ofReal
      ((2 : ℝ) ^ (-(k : ℝ) / 2) + ∑ a ∈ Finset.Icc 1 k, (2 : ℝ) ^ (-(a : ℝ) / 2)) ≤
      dimensionConstant (2 ^ k)

/-- **Beck–Spencer–Gluskin logarithmic upper bound for the Komlós constant.** There are a real
number $c > 0$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$, the
Komlós constant in dimension $n$ (the supremum of the discrepancy of real $n \times n$ matrices
whose columns all have Euclidean norm at most $1$, taken in $[0, \infty]$) is at most $c \log n$,
where $\log$ is the natural logarithm.

Source: optimization catalogue C24a, line 35, Beck, Spencer, and Gluskin. -/
theorem_wanted beckSpencerGluskinLogUpperBound_holds : beckSpencerGluskinLogUpperBound

/-- **Banaszczyk's bound for the Komlós problem.** There are a real constant $c > 0$ and a
natural number $N \ge 3$ such that for every natural number $n \ge N$, the Komlós constant in
dimension $n$ is at most $c \sqrt{\log n}$, where $\log$ is the natural logarithm.

Source: optimization catalogue C24a, line 36, Banaszczyk (1998). -/
theorem_wanted banaszczyk1998SqrtLogUpperBound_holds : banaszczyk1998SqrtLogUpperBound

/-- **Sublogarithmic bound for the Komlós problem.** For every real $\varepsilon > 0$ there is a
natural number $N \ge 3$ such that for every natural number $n \ge N$, the Komlós constant in
dimension $n$ is at most $\varepsilon \log n$, where $\log$ is the natural logarithm. In other
words, the Komlós constant in dimension $n$ is $o(\log n)$.

Source: optimization catalogue C24a, line 36, its sublogarithmic comment. -/
theorem_wanted banaszczykSublogUpperBound_holds : banaszczykSublogUpperBound

/-- **Bansal–Dadush–Garg bound for the Komlós problem, numerical form.** There are a real
constant $c > 0$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$, the
Komlós constant in dimension $n$ is at most $c \sqrt{\log n}$, where $\log$ is the natural
logarithm.

Source: BDG2019, arXiv1605.02882, retained Theorem `komlos`. -/
theorem_wanted bdg2019NumericalSqrtLogUpperBound_holds : bdg2019NumericalSqrtLogUpperBound

/-- **Bansal–Jiang bound for the Komlós problem.** There are a real constant $c > 0$, a natural
number $p$ and a natural number $N \ge 3$ such that for every natural number $n \ge N$, the
Komlós constant in dimension $n$ is at most $c (\log n)^{1/4} (\log \log n)^p$, where $\log$ is
the natural logarithm.

Source: BJ2025, arXiv2508.03961, abstract and Theorem `thm:Komlos`. -/
theorem_wanted bansalJiang2025QuarterLogUpperBound_holds : bansalJiang2025QuarterLogUpperBound

/-- **Bansal–Jiang improvement on Banaszczyk's Komlós bound.** For every real $\varepsilon > 0$
there is a natural number $N \ge 3$ such that for every natural number $n \ge N$, the Komlós
constant in dimension $n$ is at most $\varepsilon \sqrt{\log n}$, where $\log$ is the natural
logarithm. In other words, the Komlós constant in dimension $n$ is $o(\sqrt{\log n})$.

Source: BJ2025, arXiv2508.03961, the improvement reported in its abstract. -/
theorem_wanted bansalJiang2025LittleSqrtLogUpperBound_holds :
  bansalJiang2025LittleSqrtLogUpperBound

/-- Source: Kunisky, SIAM J. Discrete Math. 37 (2023), arXiv:2111.02974,
Theorem 1.1, at each dyadic dimension `2 ^ k`. -/
theorem_wanted kuniskyInfinitelyManyDimensionsLowerBound_holds :
  kuniskyInfinitelyManyDimensionsLowerBound

end KomlosDiscrepancyWanted
