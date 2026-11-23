/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrationality of the squarefree binary series (Erdős Problem 259)

Erdős Problem 259: is `∑_n μ(n)² n / 2ⁿ` irrational?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.SquarefreeBinarySeriesIrrationalErdosProblem259Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #259, https://www.erdosproblems.com/259 (status PROVED
(LEAN)). UnsolvedMath record UM-30006796 (`EP-259`), dataset ulamai/UnsolvedMath v1.8.0.

`μ` is `ArithmeticFunction.moebius`; the sum runs over `n ∈ ℕ`, and the `n = 0` term vanishes
because `μ 0 = 0`. Compared with the formal-conjectures statement `ErdosProblems/259.lean`
(identical statement; no code imported).
-/

/-- Erdős Problem 259: `∑_{n ≥ 1} μ(n)² n / 2ⁿ` is irrational (the `n = 0` term vanishes, as
`μ 0 = 0` in Mathlib). -/
def squarefreeBinarySeriesIrrational : Prop :=
  Irrational (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * n / 2 ^ n)

/--
Resolved true: Chen and Ruzsa proved that every infinite subseries of `∑ n / 2ⁿ` over squarefree `n`
is irrational, in particular this one. erdosproblems.com/259 lists the problem as proved. Source: T.
F. Bloom, Erdős Problems, Problem #259, https://www.erdosproblems.com/259 (status PROVED (LEAN));
resolution: Y.-G. Chen and I. Z. Ruzsa, On the irrationality of certain series, Period. Math.
Hungar. (1999), 31-37, erdosproblems.com/259: proved by Chen and Ruzsa, who show Erdős's stronger
conjecture that every infinite subseries over squarefree numbers is irrational,
https://www.erdosproblems.com/259.
-/
public theorem_wanted squarefreeBinarySeriesIrrational_holds : squarefreeBinarySeriesIrrational

end MathlibExt.NumberTheory.SquarefreeBinarySeriesIrrationalErdosProblem259Wanted
