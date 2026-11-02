/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

/-- **Equivalence of the square and rectangular Komlós formulations (statement).** The statement
that the uniform discrepancy bound for vectors in the unit ball holds if and only if the Komlós
constant is finite.

Source: optimization catalogue C24a, line 26, and AIM Problem 1.05. The padding
bridge is requested, not assumed or claimed definitional. -/
def constantFormulationEquivalence : Prop :=
  UniformRectangularBound ↔ komlosConstant < ⊤

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

/-- **Kunisky's lower bound for the Komlós constant (statement).** The statement that the Komlós
constant is at least $1 + \sqrt{2}$.

The bound concerns the supremum over all dimensions; it does not assert that any single
dimension attains $1 + \sqrt{2}$.

Source: optimization catalogue C24a, line 45, and retained Kunisky
arXiv2111.02974v1, Theorem 1.1. -/
def kunisky2023LowerBound : Prop :=
  ENNReal.ofReal (1 + Real.sqrt 2) ≤ komlosConstant

/-- **Infinitely many dimensions with Komlós constant at least $1 + \sqrt{2}$ (statement).** The
statement that there are infinitely many natural numbers $n \ge 1$ such that the Komlós constant
in dimension $n$ is at least $1 + \sqrt{2}$.

Source: optimization catalogue C24a, line 53. Retained Kunisky v1 only gives
a sequence approaching the endpoint from below; the journal2023 comparison
is unresolved. This request does not certify exact finite attainment. -/
def kuniskyInfinitelyManyDimensionsLowerBound : Prop :=
  {n : ℕ | 1 ≤ n ∧ ENNReal.ofReal (1 + Real.sqrt 2) ≤ dimensionConstant n}.Infinite

/-- **Komlós conjecture for vector colorings (statement).** The statement that for all natural
numbers $m$ and $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all lie in the
closed Euclidean unit ball, there are unit vectors $u_1, \dots, u_n$ in the Euclidean space
$\mathbb{R}^n$ such that $\lVert \sum_{j=1}^{n} A_{ij} u_j \rVert \le 1$ for every row index $i$,
where $\lVert \cdot \rVert$ is the Euclidean norm.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex lines 115-139,
Theorem `thm:main`. Positive column dimension is explicit. -/
def nikolov2013VectorColoringBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    ∃ u : Fin n → EuclideanSpace ℝ (Fin n), (∀ j, ‖u j‖ = 1) ∧
      ∀ i, ‖∑ j, A i j • u j‖ ≤ 1

/-- **Statement of Nikolov's bound on vector discrepancy.** This is the proposition that for all
natural numbers $m$ and $n$ with $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns
all lie in the closed Euclidean unit ball, that is, $\sum_{i} A_{ij}^2 \le 1$ for every
column $j$, the vector discrepancy of $A$ is at most $1$.

This bounds the unit-vector relaxation, not the discrepancy over sign vectors.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex, Theorem `thm:main`,
and optimization catalogue C24a, line 55. -/
def nikolov2013VectorDiscrepancyUpperBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    vectorDiscrepancy A ≤ 1

/-- **The square and rectangular Komlós formulations are equivalent.** The following two
conditions are equivalent. (a) There is a real constant $C > 0$ such that for all natural numbers
$n$ and $d$ and all vectors $v_1, \dots, v_n \in \mathbb{R}^d$ of Euclidean norm at most $1$,
writing $v_{ij}$ for the $j$-th coordinate of $v_i$, there are signs
$\varepsilon_1, \dots, \varepsilon_n \in \{-1, 1\}$ with
$\left|\sum_{i=1}^{n} \varepsilon_i v_{ij}\right| \le C$ for every coordinate index $j$. (b) The
Komlós constant, the supremum over all $n \ge 1$ of the discrepancy of real $n \times n$ matrices
whose columns all have Euclidean norm at most $1$, is finite.

Source: optimization catalogue C24a, line 26, and AIM Problem 1.05. -/
theorem_wanted constantFormulationEquivalence_holds : constantFormulationEquivalence

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

/-- **Kunisky's lower bound for the Komlós constant.** The Komlós constant (the supremum over all
$n \ge 1$ of the discrepancy of real $n \times n$ matrices whose columns all have Euclidean norm
at most $1$, taken in $[0, \infty]$) is at least $1 + \sqrt{2}$.

Source: Kunisky, arXiv2111.02974v1, Theorem 1.1; catalogue C24a, line 45. -/
theorem_wanted kunisky2023LowerBound_holds : kunisky2023LowerBound

/-- **Infinitely many dimensions have Komlós constant at least $1 + \sqrt{2}$.** There are
infinitely many natural numbers $n \ge 1$ such that the Komlós constant in dimension $n$ (the
supremum of the discrepancy of real $n \times n$ matrices whose columns all have Euclidean norm
at most $1$, taken in $[0, \infty]$) is at least $1 + \sqrt{2}$.

Source: catalogue C24a, line 53, unverified exact finite-endpoint assertion. -/
theorem_wanted kuniskyInfinitelyManyDimensionsLowerBound_holds :
  kuniskyInfinitelyManyDimensionsLowerBound

/-- **Nikolov's theorem: the Komlós conjecture holds for vector colorings.** For all natural
numbers $m$ and $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all have Euclidean
norm at most $1$, there are unit vectors $u_1, \dots, u_n$ in the Euclidean space $\mathbb{R}^n$
such that $\lVert \sum_{j=1}^{n} A_{ij} u_j \rVert \le 1$ for every row index $i$, where
$\lVert \cdot \rVert$ is the Euclidean norm.

Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`. -/
theorem_wanted nikolov2013VectorColoringBound_holds : nikolov2013VectorColoringBound

/-- **Nikolov's bound on vector discrepancy.** For all natural numbers $m$ and $n$ with
$n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all lie in the closed
Euclidean unit ball, that is, $\sum_{i} A_{ij}^2 \le 1$ for every column $j$, the vector
discrepancy of $A$ is at most $1$.

Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`; catalogue line 55. -/
theorem_wanted nikolov2013VectorDiscrepancyUpperBound_holds :
  nikolov2013VectorDiscrepancyUpperBound

end KomlosDiscrepancyWanted
