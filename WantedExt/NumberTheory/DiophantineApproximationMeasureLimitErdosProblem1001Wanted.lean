/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Limit measure of well-approximable numbers in a dyadic range (Erdős Problem 1001)

Erdős Problem 1001 (Erdős, Szüsz and Turán): let `S(N, A, c)` be the measure of the set of `α ∈ (0,
1)` with `|α - x / y| < A / y²` for some coprime `x, y` with `N ≤ y ≤ c N`. Does `lim_{N → ∞} S(N,
A, c) = f(A, c)` exist? What is its explicit form?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.NumberTheory.DiophantineApproximationMeasureLimitErdosProblem1001Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1001, https://www.erdosproblems.com/1001 (status
SOLVED). UnsolvedMath record UM-30007119 (`EP-1001`), dataset ulamai/UnsolvedMath v1.8.0.

The parameters range over `A > 0` and `c > 1`, as in Erdős, Szüsz and Turán and in the resolving
papers. `x` is an integer and `y` a natural number; the measure is Lebesgue measure on `ℝ` of a
subset of `(0, 1)`. Only the existence question is formalized; the explicit form (computed by Boca
and by Xiong and Zaharescu) is not.
-/

/-- `S(N, A, c)`: the set of `α ∈ (0, 1)` with `|α - x / y| < A / y²` for some coprime integers
`x`, `y` with `N ≤ y ≤ c N`. -/
def approximableSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α | α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ x : ℤ, ∃ y : ℕ, (N : ℝ) ≤ y ∧ (y : ℝ) ≤ c * N ∧
    Int.gcd x y = 1 ∧ |α - x / y| < A / (y : ℝ) ^ 2}

/-- Erdős Problem 1001 (existence part): for all `A > 0` and `c > 1` the Lebesgue measure of
`S(N, A, c)` converges as `N → ∞`. -/
def approximableMeasureLimitExists : Prop :=
  ∀ A c : ℝ, 0 < A → 1 < c → ∃ L : ENNReal,
    Filter.Tendsto (fun N : ℕ => MeasureTheory.volume (approximableSet N A c)) Filter.atTop
      (nhds L)

/--
Resolved true: Kesten and Sós proved that `S(N, A, c)` converges as `N → ∞` for all `A > 0` and `c >
1`; Boca and, independently, Xiong and Zaharescu gave direct proofs identifying the limit. Source:
T. F. Bloom, Erdős Problems, Problem #1001, https://www.erdosproblems.com/1001 (status SOLVED);
resolution: H. Kesten and V. T. Sós, On two problems of Erdős, Szüsz and Turán concerning
diophantine approximations, Acta Arith. (1966/67), 183-192, existence of lim S(N, A, c) for all A >
0 and c > 1 (erdosproblems.com/1001; restated in F. P. Boca, Int. J. Number Theory (2008), 691-708),
https://www.erdosproblems.com/1001.
-/
public theorem_wanted approximableMeasureLimitExists_holds : approximableMeasureLimitExists

end MathlibExt.NumberTheory.DiophantineApproximationMeasureLimitErdosProblem1001Wanted
