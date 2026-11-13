/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ratios of consecutive divisor counts are dense (Erdős Problem 964)

Erdős Problem 964: let `τ(n)` count the number of divisors of `n`. Is the sequence `τ(n + 1)/τ(n)`
everywhere dense in `(0, ∞)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorCountRatioDenseErdosProblem964Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #964, https://www.erdosproblems.com/964 (status PROVED
(LEAN)). UnsolvedMath record UM-30007101 (`EP-964`), dataset ulamai/UnsolvedMath v1.8.0.

`τ(n)` is `n.divisors.card` and `n ≥ 1`; dense in `(0, ∞)` means that every interval `(a, b)` with
`0 < a < b` contains a term. Compared with the formal-conjectures statement `ErdosProblems/964.lean`
(`erdos_964`, equivalent; no code imported).
-/

/-- Erdős Problem 964: the values `τ(n + 1) / τ(n)` (`n ≥ 1`, `τ` the number of divisors) are dense
in `(0, ∞)`: every interval `(a, b)` with `0 < a < b` contains one of them. -/
def divisorCountRatioDense : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ n : ℕ, 1 ≤ n ∧
    a < ((n + 1).divisors.card : ℝ) / n.divisors.card ∧
      ((n + 1).divisors.card : ℝ) / n.divisors.card < b

/--
Resolved true: Eberhard proved that `τ(n + 1)/τ(n)` attains every positive rational value
(infinitely often), and the positive rationals are dense in `(0, ∞)`; erdosproblems.com/964 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #964,
https://www.erdosproblems.com/964 (status PROVED (LEAN)); resolution: S. Eberhard, Ratios of
consecutive values of the divisor function, arXiv:2505.00727 (2025), abstract: the sequence d(n +
1)/d(n) attains every positive rational infinitely many times; erdosproblems.com/964,
https://arxiv.org/abs/2505.00727.
-/
public theorem_wanted divisorCountRatioDense_holds : divisorCountRatioDense

end MathlibExt.NumberTheory.DivisorCountRatioDenseErdosProblem964Wanted
