/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integers with a divisor in (n, 2n) (Erdős Problem 446)

Erdős Problem 446: let `δ(n)` be the density of the integers with a divisor in `(n, 2n)`. What is
the growth rate of `δ(n)`? If `δ₁(n)` is the density of the integers with exactly one divisor in
`(n, 2n)`, is `δ₁(n) = o(δ(n))`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorInDyadicIntervalErdosProblem446Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #446, https://www.erdosproblems.com/446 (status
SOLVED). UnsolvedMath record UM-30006876 (`EP-446`), dataset ulamai/UnsolvedMath v1.8.0.

Densities are natural densities (`Set.HasDensity`, MathlibExt); they exist because membership
depends only on the residue modulo the product of the `d ∈ (n, 2n)`. The growth rate is Ford's `δ(n)
≍ (log n)^{-α} (log log n)^{-3/2}`, `α = 1 - (1 + log log 2)/log 2`. Ford counts divisors in `(n,
2n]`; the sets differ only on multiples of `2n`, of density `1/(2n) = o(δ(n))`. The second claim
quantifies over the density functions, so its refutation asserts that they exist. formal-conjectures
has no statement of this problem.
-/

open Asymptotics

/-- The integers with a divisor in `(n, 2n)`. -/
def withDivisorIn (n : ℕ) : Set ℕ :=
  {m | ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m}

/-- The integers with exactly one divisor in `(n, 2n)`. -/
def withOneDivisorIn (n : ℕ) : Set ℕ :=
  {m | ((Finset.Ioo n (2 * n)).filter (· ∣ m)).card = 1}

/-- Ford's exponent `α = 1 - (1 + log log 2) / log 2 = 0.086…`. -/
noncomputable def fordExponent : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- Erdős Problem 446, first question (growth rate of `δ(n)`): the density `δ(n)` of the integers
with a divisor in `(n, 2n)` exists and `δ(n) ≍ (log n)^(-α) (log log n)^(-3/2)`. -/
def dyadicDivisorDensityGrowth : Prop :=
  ∃ δ : ℕ → ℝ, (∀ n, (withDivisorIn n).HasDensity (δ n)) ∧
    δ =Θ[Filter.atTop] fun n : ℕ =>
      1 / (Real.log n ^ fordExponent * Real.log (Real.log n) ^ (3 / 2 : ℝ))

/-- Erdős Problem 446, second question: `δ₁(n) = o(δ(n))`, where `δ₁(n)` is the density of the
integers with exactly one divisor in `(n, 2n)`. -/
def exactlyOneDivisorDensityNegligible : Prop :=
  ∀ δ δ₁ : ℕ → ℝ, (∀ n, (withDivisorIn n).HasDensity (δ n)) →
    (∀ n, (withOneDivisorIn n).HasDensity (δ₁ n)) → δ₁ =o[Filter.atTop] δ

/--
Resolved true: Ford determined the growth rate `δ(n) ≍ (log n)^{-α} (log log n)^{-3/2}` with `α =
1 - (1 + log log 2)/log 2 = 0.086…`, refining Erdős's `δ(n) = (log n)^{-α + o(1)}` and Tenenbaum's
estimates (erdosproblems.com/446). Source: T. F. Bloom, Erdős Problems, Problem #446,
https://www.erdosproblems.com/446 (status SOLVED); resolution: K. Ford, The distribution of
integers with a divisor in a given interval, Ann. of Math. (2) 168 (2008), 367-433, δ(n) ≍ (log
n)^{-α} (log log n)^{-3/2}, and δ_r(n) ≫_r δ(n) (erdosproblems.com/446).
-/
public theorem_wanted dyadicDivisorDensityGrowth_holds : dyadicDivisorDensityGrowth

/--
Resolved false: Ford proved that the density `δ_r(n)` of the integers with exactly `r` divisors in
`(n, 2n)` satisfies `δ_r(n) ≫_r δ(n)`; for `r = 1` this rules out `δ₁(n) = o(δ(n))`, which Erdős had
expected (erdosproblems.com/446). Source: T. F. Bloom, Erdős Problems, Problem #446,
https://www.erdosproblems.com/446 (status SOLVED); resolution: K. Ford, The distribution of integers
with a divisor in a given interval, Ann. of Math. (2) 168 (2008), 367-433, δ(n) ≍ (log n)^{-α} (log
log n)^{-3/2}, and δ_r(n) ≫_r δ(n) (erdosproblems.com/446).
-/
public theorem_wanted exactlyOneDivisorDensityNegligible_refuted :
    ¬ exactlyOneDivisorDensityNegligible

end MathlibExt.NumberTheory.DivisorInDyadicIntervalErdosProblem446Wanted
