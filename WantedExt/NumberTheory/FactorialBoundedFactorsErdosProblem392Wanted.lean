/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Factoring n! into factors at most n² (Erdős Problem 392)

Erdős Problem 392: let `A(n)` be the least `t` such that `n! = a₁ ⋯ aₜ` with `a₁ ≤ ⋯ ≤ aₜ ≤ n²`. Is
`A(n) = n/2 - n/(2 log n) + o(n / log n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialBoundedFactorsErdosProblem392Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #392, https://www.erdosproblems.com/392 (status PROVED
(LEAN)). UnsolvedMath record UM-30006850 (`EP-392`), dataset ulamai/UnsolvedMath v1.8.0.

`A(n)` is the least number of factors, each at most `n²`, with product `n!` (the order of the
factors is irrelevant); `log` is the natural logarithm. Compared with the formal-conjectures
statement `ErdosProblems/392.lean` (equivalent; there `A` is a hypothesis-characterized function; no
code imported).
-/

open Asymptotics

/-- `A(n)`: the least `t` such that `n! = a₁ ⋯ aₜ` with every factor `aᵢ ≤ n²`. -/
noncomputable def leastBoundedFactorCount (n : ℕ) : ℕ :=
  sInf {t : ℕ | ∃ a : Fin t → ℕ, ∏ i, a i = Nat.factorial n ∧ ∀ i, a i ≤ n ^ 2}

/-- Erdős Problem 392: `A(n) = n / 2 - n / (2 log n) + o(n / log n)`. -/
def leastBoundedFactorCountAsymptotic : Prop :=
  (fun n : ℕ => (leastBoundedFactorCount n : ℝ) - ((n : ℝ) / 2 - n / (2 * Real.log n)))
    =o[Filter.atTop] fun n : ℕ => (n : ℝ) / Real.log n

/--
Resolved true: Cambie observed (erdosproblems.com/392) that pairing the factors of the greedy
decomposition with all factors at most `n`, which has `n - n/log n + o(n/log n)` factors, gives the
upper bound, while `A(n) ≥ log n! / log n²` and Stirling's formula give the lower bound; the
statement has a Lean proof in the PrimeNumberTheoremAnd project. Source: T. F. Bloom, Erdős
Problems, Problem #392, https://www.erdosproblems.com/392 (status PROVED (LEAN)); resolution: S.
Cambie, comment on erdosproblems.com/392; Lean proof in PrimeNumberTheoremAnd,
PrimeNumberTheoremAnd/IEANTN/Erdos392.lean, pair the factors of the greedy decomposition with
factors at most n, which has n - n/log n + o(n/log n) factors; the lower bound is Stirling's
formula,
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/d82a35ecc798ada27f82a88b559f25b753f63a73/PrimeNumberTheoremAnd/IEANTN/Erdos392.lean.
-/
public theorem_wanted leastBoundedFactorCountAsymptotic_holds : leastBoundedFactorCountAsymptotic

end MathlibExt.NumberTheory.FactorialBoundedFactorsErdosProblem392Wanted
