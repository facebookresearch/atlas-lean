/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrationality of `∑ ω(n) / 2^n` (Erdős Problem 69)

Erdős Problem 69: is `∑_{n ≥ 2} ω(n) / 2^n` irrational? (Here `ω(n)` counts the number of distinct
prime divisors of `n`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.OmegaPowerSeriesIrrationalErdosProblem69Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #69, https://www.erdosproblems.com/69 (status PROVED).
UnsolvedMath record UM-30006709 (`EP-69`), dataset ulamai/UnsolvedMath v1.8.0.

`ω(n)` is `n.primeFactors.card`; the series is written over `n + 2` for `n ≥ 0` and converges
absolutely, so the `tsum` is its value. Compared with the formal-conjectures statement
`ErdosProblems/69.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 69: `∑_{n ≥ 2} ω(n) / 2^n` is irrational, where `ω(n)` is the number of distinct
prime divisors of `n` (the series converges since `ω(n) ≤ n`). -/
def omegaPowerSeriesIrrational : Prop :=
  Irrational (∑' n : ℕ, ((n + 2).primeFactors.card : ℝ) / 2 ^ (n + 2))

/--
Resolved true: Tao and Teräväinen proved that `∑_{n ≥ 1} ω(n) / 2^n` (equal to `∑_p 1 / (2^p - 1)`)
is irrational; erdosproblems.com/69 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #69, https://www.erdosproblems.com/69 (status PROVED); resolution: T. Tao and J.
Teräväinen, Quantitative correlations and some problems on prime factors of consecutive integers,
arXiv:2512.01739 (2025), abstract: the series ∑_{n ≥ 1} ω(n) / 2^n is irrational, settling a
conjecture of Erdős; erdosproblems.com/69: proved irrational unconditionally by Tao and Teräväinen,
https://arxiv.org/abs/2512.01739.
-/
public theorem_wanted omegaPowerSeriesIrrational_holds : omegaPowerSeriesIrrational

end MathlibExt.NumberTheory.OmegaPowerSeriesIrrationalErdosProblem69Wanted
