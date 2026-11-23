/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrationality of `∑ σ(n) / 2^n` (Erdős Problem 250)

Erdős Problem 250: is `∑_{n ≥ 1} σ(n) / 2^n` irrational?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorSumBinarySeriesIrrationalErdosProblem250Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #250, https://www.erdosproblems.com/250 (status PROVED
(LEAN)). UnsolvedMath record UM-30006793 (`EP-250`), dataset ulamai/UnsolvedMath v1.8.0.

`σ(n)` is `ArithmeticFunction.sigma 1 n` with `σ(0) = 0`; the series converges since `σ(n) ≤ n²`, so
the `tsum` is its sum. Compared with the formal-conjectures statement `ErdosProblems/250.lean`
(every `HasSum` limit is irrational, equivalent; no code imported).
-/

/-- Erdős Problem 250: the number `∑_{n ≥ 1} σ(n) / 2^n` is irrational (`σ(0) = 0` in Mathlib, so
the `n = 0` term vanishes). -/
def divisorSumBinarySeriesIrrational : Prop :=
  Irrational (∑' n : ℕ, (ArithmeticFunction.sigma 1 n : ℝ) / 2 ^ n)

/--
Resolved true: `∑ σ(n) qⁿ = (1 - P(q)) / 24` for the Eisenstein series `P = E₂`, and Nesterenko's
theorem makes `P(1/2)` transcendental, so the sum is irrational (indeed transcendental);
erdosproblems.com/250 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#250, https://www.erdosproblems.com/250 (status PROVED (LEAN)); resolution: Yu. V. Nesterenko,
Modular functions and transcendence questions, Sb. Math. 187 (1996), 1319-1348, algebraic
independence of q, P(q), Q(q), R(q) for algebraic 0 < |q| < 1; erdosproblems.com/250: answered yes
by Nesterenko, https://doi.org/10.1070/SM1996v187n09ABEH000158.
-/
public theorem_wanted divisorSumBinarySeriesIrrational_holds : divisorSumBinarySeriesIrrational

end MathlibExt.NumberTheory.DivisorSumBinarySeriesIrrationalErdosProblem250Wanted
