/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consecutive divisor ratios (Erdős Problem 1099)

Erdős Problem 1099: for the divisors `1 = d₁ < ⋯ < d_τ(n) = n` and `α > 1` let `h_α(n) = ∑ᵢ (dᵢ₊₁/dᵢ
- 1)^α`. Is `liminf_{n → ∞} h_α(n) ≪_α 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorRatioPowerSumErdosProblem1099Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1099, https://www.erdosproblems.com/1099 (status
PROVED). UnsolvedMath record UM-30007162 (`EP-1099`), dataset ulamai/UnsolvedMath v1.8.0.

`liminf h_α(n) < ∞` is "`h_α(n) ≤ C_α` for infinitely many `n`" (the liminf is at least `1`). The
successor of a divisor `d < n` is the least divisor of `n` exceeding `d`. Compared with the
formal-conjectures statement `ErdosProblems/1099.lean` (equivalent; no code imported).
-/

/-- The divisor of `n` that follows `d`: the least divisor of `n` exceeding `d`. -/
noncomputable def nextDivisor (n d : ℕ) : ℕ :=
  sInf {e | e ∣ n ∧ d < e}

/-- `h_α(n) = ∑ᵢ (dᵢ₊₁ / dᵢ - 1) ^ α` over consecutive divisors `dᵢ < dᵢ₊₁` of `n`. -/
noncomputable def divisorRatioPowerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· < n), ((nextDivisor n d : ℝ) / d - 1) ^ α

/-- Erdős Problem 1099: for every `α > 1`, `liminf_{n → ∞} h_α(n) < ∞`, i.e. `h_α(n)` stays below
some constant `C_α` for infinitely many `n`. -/
def divisorRatioPowerSumLiminfFinite : Prop :=
  ∀ α : ℝ, 1 < α → ∃ C : ℝ, ∃ᶠ n in Filter.atTop, divisorRatioPowerSum α n ≤ C

/--
Resolved true: Vose constructed a sequence of integers `n` along which `h_α(n)` stays bounded;
erdosproblems.com/1099 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1099, https://www.erdosproblems.com/1099 (status PROVED); resolution: M. D. Vose, Integers with
consecutive divisors in small ratio, J. Number Theory 19 (1984), 233-238, erdosproblems.com/1099:
positive answer by Vose's explicit sequence, https://doi.org/10.1016/0022-314X(84)90107-4.
-/
public theorem_wanted divisorRatioPowerSumLiminfFinite_holds : divisorRatioPowerSumLiminfFinite

end MathlibExt.NumberTheory.DivisorRatioPowerSumErdosProblem1099Wanted
