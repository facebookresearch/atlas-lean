/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Factorials dividing n! times powers of small primes (Erdős Problem 401)

Erdős Problem 401: is there `f(r) → ∞` such that for each `r` there are infinitely many `n` with
some `a₁, a₂` satisfying `a₁ + a₂ > n + f(r) log n` and `a₁! a₂! ∣ n! 2ⁿ 3ⁿ ⋯ p_rⁿ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialProductDivisibilityErdosProblem401Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #401, https://www.erdosproblems.com/401 (status PROVED
(LEAN)). UnsolvedMath record UM-30006855 (`EP-401`), dataset ulamai/UnsolvedMath v1.8.0.

The quantifier order is the one erdosproblems.com takes as intended (`f` first, then `r`, then
infinitely many `n`); `p_r` is the `r`-th prime, `r ≥ 1`, and `a₁, a₂` are positive. Compared with
the formal-conjectures statement `ErdosProblems/401.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 401: there is `f` with `f(r) → ∞` such that for every `r ≥ 1` there are
infinitely many `n` admitting positive `a₁, a₂` with `a₁ + a₂ > n + f(r) log n` and
`a₁! a₂! ∣ n! 2ⁿ 3ⁿ ⋯ p_rⁿ`, where `p_r` is the `r`-th prime. -/
def factorialProductDivisibility : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧ ∀ r : ℕ, 1 ≤ r →
    {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧ (n : ℝ) + f r * Real.log n < a₁ + a₂ ∧
      Nat.factorial a₁ * Nat.factorial a₂ ∣
        Nat.factorial n * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite

/--
Resolved true: Barreto and Leeham (using ChatGPT) proved the statement with this quantifier order,
with a Lean proof (plby/lean-proofs, `Erdos401.lean`); Sothanaphan refuted the variant with "for all
large `n`". erdosproblems.com/401 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #401, https://www.erdosproblems.com/401 (status PROVED (LEAN)); resolution: K. Barreto and
Leeham (using ChatGPT), erdosproblems.com/401; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos401.lean, proof of the stated problem, by the construction of their
solution to Problem 729,
https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos401.lean.
-/
public theorem_wanted factorialProductDivisibility_holds : factorialProductDivisibility

end MathlibExt.NumberTheory.FactorialProductDivisibilityErdosProblem401Wanted
