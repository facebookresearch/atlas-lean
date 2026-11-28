/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.DivisorApproximantPrimeCounting
public import MathlibExt.NumberTheory.PrimeCountingFromDivisors

/-!
# Smooth approximants of divisor functions and `π(n)` (statements)

Statement-only targets from Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula
for π(n) with the Divisor Counting Function*. The paper approximates the divisibility indicator
`[k | n]` by `exp(-n k A(k, n) sin²(nπ/k))`, where `A(k, n) sin²(nπ/k) ≥ 1` whenever `k ∤ n`.
The extraction drops the accent that distinguishes each approximant from the exact function;
the approximant is always the quantity being defined. `τ(n) = n.divisors.card`,
`σ(n) = ∑_{d ∣ n} d`, `π(n) = Nat.primeCounting n`. The paper's `A : ℕ × ℕ → ℝ⁺` is a
function `ℕ → ℕ → ℝ`; its positivity is not needed and not assumed.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- **Prime-counting function from the smooth divisor count.** For a natural number $k$ let
$$\tilde\tau(k) = \sum_{j=1}^{k} \exp\left(-(\pi/2)^2 k j^3 \sin^2\frac{k\pi}{j}\right),$$
and for $n \ge 2$ let $\tilde\pi(n) = \sum_{k=2}^{n} e^{-k(\tilde\tau(k) - 2)}$. Then for every
natural number $n \ge 2$, $|\tilde\pi(n) - \pi(n)| < 0.7129749140934$, where $\pi(n)$ is the
number of primes at most $n$.

The constant is $0.684 + 1/(e^3(e - 1))$ truncated to thirteen decimal places, the sum of the
two one-sided bounds, as the two-sided bound requires.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 2
(`integers-2026-A46-thm-2`). -/
public theorem_wanted primeCountingApprox_abs_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    let τ' : ℕ → ℝ := fun k => ∑ j ∈ Icc 1 k,
      Real.exp (-((Real.pi / 2) ^ 2 * k * j ^ 3 * Real.sin (k * Real.pi / j) ^ 2))
    |∑ k ∈ Icc 2 n, Real.exp (-(k * (τ' k - 2))) - Nat.primeCounting n| < 0.7129749140934

end

end MetaMathlibExt
