/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ratios of integers with equal divisor sums (Erdős Problem 823)

Erdős Problem 823: let `α ≥ 1`. Is there a sequence of integers `n_k, m_k` such that `n_k / m_k → α`
and `σ(n_k) = σ(m_k)` for all `k ≥ 1`, where `σ` is the sum of divisors function?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.EqualDivisorSumRatioErdosProblem823Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #823, https://www.erdosproblems.com/823 (status
PROVED). UnsolvedMath record UM-30007051 (`EP-823`), dataset ulamai/UnsolvedMath v1.8.0.

The `n_k`, `m_k` are positive integers and `σ = ArithmeticFunction.sigma 1`. The problem allows `α =
1`, which `n_k = m_k` meets trivially, so the target takes `α > 1` (the limit then forces `n_k ≠
m_k` for all large `k`). Pollack's Theorem 1 covers every real `β > 0`. formal-conjectures has no
statement of this problem.
-/

/-- Erdős Problem 823 for `α > 1` (`α = 1` is met by `n_k = m_k`): for every real `α > 1` there
are sequences of positive integers `n_k`, `m_k` with `n_k / m_k → α` and `σ(n_k) = σ(m_k)` for
all `k`. -/
def equalDivisorSumRatios : Prop :=
  ∀ α : ℝ, 1 < α → ∃ a b : ℕ → ℕ, (∀ k, 0 < a k ∧ 0 < b k ∧
      ArithmeticFunction.sigma 1 (a k) = ArithmeticFunction.sigma 1 (b k)) ∧
    Filter.Tendsto (fun k => (a k : ℝ) / b k) Filter.atTop (nhds α)

/--
Resolved true: Pollack proved that every positive real number is a limit of ratios `m / n` with
`σ(m) = σ(n)` (Theorem 1; Erdős wrote that the analogue for `φ` is easy); erdosproblems.com/823
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #823,
https://www.erdosproblems.com/823 (status PROVED); resolution: P. Pollack, Remarks on fibers of the
sum-of-divisors function, in Analytic Number Theory, in honor of Helmut Maier's 60th birthday,
Springer (2015), 305-320, Theorem 1: for every β > 0 and every ε > 0 there are integers m and n with
σ(m) = σ(n) and |m/n - β| < ε, answering in the affirmative a 1959 question of Erdős,
https://www.pollack-math.net/preimages-maier3.pdf.
-/
public theorem_wanted equalDivisorSumRatios_holds : equalDivisorSumRatios

end MathlibExt.NumberTheory.EqualDivisorSumRatioErdosProblem823Wanted
