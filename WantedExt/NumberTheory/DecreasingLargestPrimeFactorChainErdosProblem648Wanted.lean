/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Increasing integers with decreasing largest prime factors (Erdős Problem 648)

Erdős Problem 648: let `g(n)` denote the largest `t` such that there exist integers `2 ≤ a₁ < a₂ < ⋯
< a_t < n` with `P(a₁) > P(a₂) > ⋯ > P(a_t)`, where `P(m)` is the greatest prime factor of `m`.
Estimate `g(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DecreasingLargestPrimeFactorChainErdosProblem648Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #648, https://www.erdosproblems.com/648 (status SOLVED
(LEAN)). UnsolvedMath record UM-30006968 (`EP-648`), dataset ulamai/UnsolvedMath v1.8.0.

'Estimate `g(n)`' is formalized as Cambie's order `g(n) ≍ (n / log n)^{1/2}` (`Asymptotics.IsTheta`
at `atTop`); his follow-up question whether `g(n) ∼ c (n / log n)^{1/2}` is open and not stated.
`P(m)` is written `m.primeFactors.sup id`, the largest element of `m.primeFactors` (`0` for
`m ≤ 1`), correct for `m ≥ 2`. Compared with the formal-conjectures statement
`ErdosProblems/648.lean` (equivalent; no code imported).
-/

/-- `g(n)`: the largest `t` such that there are integers `2 ≤ a₁ < a₂ < ⋯ < a_t < n` with
`P(a₁) > P(a₂) > ⋯ > P(a_t)` (bounded by `n`). -/
noncomputable def decreasingPrimeFactorChain (n : ℕ) : ℕ :=
  sSup {t | ∃ a : Fin t → ℕ, StrictMono a ∧ (∀ i, 2 ≤ a i ∧ a i < n) ∧
    StrictAnti fun i => (a i).primeFactors.sup id}

/-- Erdős Problem 648, in the form of its solution: `g(n) ≍ (n / log n)^{1/2}`. -/
def decreasingPrimeFactorChainOrder : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (decreasingPrimeFactorChain n : ℝ))
    fun n => Real.sqrt (n / Real.log n)

/--
Resolved true: Cambie proved `g(n) ≍ (n / log n)^{1/2}` (whether `g(n) ∼ c (n / log n)^{1/2}`,
necessarily with `2 ≤ c ≤ 2√2`, is open); erdosproblems.com/648 lists the problem as solved, with a
Lean proof of the formal-conjectures statement. Source: T. F. Bloom, Erdős Problems, Problem #648,
https://www.erdosproblems.com/648 (status SOLVED (LEAN)); resolution: S. Cambie, On Erdős problem
#648, arXiv:2503.22691 (2025), erdosproblems.com/648: Cambie proved g(n) ≍ (n / log n)^{1/2};
abstract: 'We establish the order of the maximum length of an increasing sequence, bounded by n, in
which the largest prime divisor of the elements form a decreasing sequence',
https://arxiv.org/abs/2503.22691.
-/
public theorem_wanted decreasingPrimeFactorChainOrder_holds : decreasingPrimeFactorChainOrder

end MathlibExt.NumberTheory.DecreasingLargestPrimeFactorChainErdosProblem648Wanted
