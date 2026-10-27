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

/-- The square-constant and uniform rectangular formulations agree.

Source: optimization catalogue C24a, line 26, and AIM Problem 1.05. The padding
bridge is requested, not assumed or claimed definitional. -/
def constantFormulationEquivalence : Prop :=
  UniformRectangularBound ↔ komlosConstant < ⊤

/-- One positive universal multiplier gives the logarithmic upper bound.

Source: optimization catalogue C24a, line 35, Beck (1981), Spencer (1985), and
Gluskin (1989); their full original theorem texts remain a primary-source gap. -/
def beckSpencerGluskinLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.log n)

/-- Banaszczyk's square-root-logarithmic bound with one universal multiplier.

Source: optimization catalogue C24a, line 36, Banaszczyk (1998), also reported
in retained BJ2025 introduction and BDG2019 Theorem `komlos`. -/
def banaszczyk1998SqrtLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.sqrt (Real.log n))

/-- The source's sublogarithmic improvement, with every positive epsilon.

Source: optimization catalogue C24a, line 36, the `o(log n)` comment. -/
def banaszczykSublogUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (ε * Real.log n)

/-- Only the numerical consequence, not an encoded polynomial-time algorithm.

Source: Bansal, Dadush, and Garg, arXiv1605.02882, retained introduction lines
52-60, Theorem `komlos`; efficient randomized/high-probability computation is
an explicit separate gap. -/
def bdg2019NumericalSqrtLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (c * Real.sqrt (Real.log n))

/-- Quarter-log order with an unspecified polynomial degree in `log log n`.

Source: Bansal and Haotian Jiang, arXiv2508.03961, retained abstract lines 1-9
and introduction Theorem `thm:Komlos`. The abstract explicitly defines tilde
as `poly(log log n)`; no degree is invented. -/
def bansalJiang2025QuarterLogUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ p : ℕ, ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal
      (c * (Real.log n) ^ (1 / 4 : ℝ) * (Real.log (Real.log n)) ^ p)

/-- The quarter-log theorem improves square-root-log order asymptotically.

Source: optimization catalogue C24a, line 38, and BJ2025's retained abstract. -/
def bansalJiang2025LittleSqrtLogUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    dimensionConstant n ≤ ENNReal.ofReal (ε * Real.sqrt (Real.log n))

/-- Kunisky's global lower endpoint, without finite-dimensional attainment.

Source: optimization catalogue C24a, line 45, and retained Kunisky
arXiv2111.02974v1, Theorem 1.1. -/
def kunisky2023LowerBound : Prop :=
  ENNReal.ofReal (1 + Real.sqrt 2) ≤ komlosConstant

/-- The catalogue's literal infinite-dimension endpoint assertion is unverified.

Source: optimization catalogue C24a, line 53. Retained Kunisky v1 only gives
a sequence approaching the endpoint from below; the journal2023 comparison
is unresolved. This request does not certify exact finite attainment. -/
def kuniskyInfinitelyManyDimensionsLowerBound : Prop :=
  {n : ℕ | 1 ≤ n ∧ ENNReal.ofReal (1 + Real.sqrt 2) ≤ dimensionConstant n}.Infinite

/-- Nikolov's actual unit-vector witness for admitted rectangular matrices.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex lines 115-139,
Theorem `thm:main`. Positive column dimension is explicit. -/
def nikolov2013VectorColoringBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    ∃ u : Fin n → EuclideanSpace ℝ (Fin n), (∀ j, ‖u j‖ = 1) ∧
      ∀ i, ‖∑ j, A i j • u j‖ ≤ 1

/-- The unit-vector relaxation optimum is at most one, not the sign optimum.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex, Theorem `thm:main`,
and optimization catalogue C24a, line 55. -/
def nikolov2013VectorDiscrepancyUpperBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    vectorDiscrepancy A ≤ 1

/-- Source: optimization catalogue C24a, line 26, and AIM Problem 1.05. -/
theorem_wanted constantFormulationEquivalence_holds : constantFormulationEquivalence

/-- Source: optimization catalogue C24a, line 35, Beck, Spencer, and Gluskin. -/
theorem_wanted beckSpencerGluskinLogUpperBound_holds : beckSpencerGluskinLogUpperBound

/-- Source: optimization catalogue C24a, line 36, Banaszczyk (1998). -/
theorem_wanted banaszczyk1998SqrtLogUpperBound_holds : banaszczyk1998SqrtLogUpperBound

/-- Source: optimization catalogue C24a, line 36, its sublogarithmic comment. -/
theorem_wanted banaszczykSublogUpperBound_holds : banaszczykSublogUpperBound

/-- Source: BDG2019, arXiv1605.02882, retained Theorem `komlos`. -/
theorem_wanted bdg2019NumericalSqrtLogUpperBound_holds : bdg2019NumericalSqrtLogUpperBound

/-- Source: BJ2025, arXiv2508.03961, abstract and Theorem `thm:Komlos`. -/
theorem_wanted bansalJiang2025QuarterLogUpperBound_holds : bansalJiang2025QuarterLogUpperBound

/-- Source: BJ2025, arXiv2508.03961, the improvement reported in its abstract. -/
theorem_wanted bansalJiang2025LittleSqrtLogUpperBound_holds :
  bansalJiang2025LittleSqrtLogUpperBound

/-- Source: Kunisky, arXiv2111.02974v1, Theorem 1.1; catalogue C24a, line 45. -/
theorem_wanted kunisky2023LowerBound_holds : kunisky2023LowerBound

/-- Source: catalogue C24a, line 53, unverified exact finite-endpoint assertion. -/
theorem_wanted kuniskyInfinitelyManyDimensionsLowerBound_holds :
  kuniskyInfinitelyManyDimensionsLowerBound

/-- Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`. -/
theorem_wanted nikolov2013VectorColoringBound_holds : nikolov2013VectorColoringBound

/-- Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`; catalogue line 55. -/
theorem_wanted nikolov2013VectorDiscrepancyUpperBound_holds :
  nikolov2013VectorDiscrepancyUpperBound

end KomlosDiscrepancyWanted
