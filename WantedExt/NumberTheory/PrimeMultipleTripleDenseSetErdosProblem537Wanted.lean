/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal prime multiples in dense sets (Erdős Problem 537)

Erdős Problem 537: for `ε > 0` and large `N`, must every `A ⊆ {1, …, N}` with `|A| ≥ ε N` contain
`a₁, a₂, a₃` with `a₁ p₁ = a₂ p₂ = a₃ p₃` for distinct primes `p₁, p₂, p₃`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeMultipleTripleDenseSetErdosProblem537Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #537, https://www.erdosproblems.com/537 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006922 (`EP-537`), dataset ulamai/UnsolvedMath v1.8.0.

The `aᵢ` are automatically distinct (distinct primes). The claim quantifies over all `ε > 0`, so its
refutation needs one `ε`. Compared with the formal-conjectures statement `ErdosProblems/537.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 537: for every `ε > 0` and all large `N`, every `A ⊆ {1, …, N}` with
`|A| ≥ ε N` contains `a₁, a₂, a₃` with `a₁ p₁ = a₂ p₂ = a₃ p₃` for distinct primes
`p₁, p₂, p₃`. -/
def denseSetHasPrimeMultipleTriple : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    ε * N ≤ (A.card : ℝ) →
      ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
        p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃

/--
Resolved false: Ruzsa's set of squarefree `p₁ ⋯ p_r` with `pᵢ₊₁ > 2 pᵢ` has positive density, and
its elements in `(N/2, N)` contain no such triple: if `a₂ > a₃` then `p₂ < p₃`, `p₂ p₃ ∣ a₁` forces
`p₃ / p₂ > 2`, while `p₃ / p₂ = a₂ / a₃ < 2`. Source: T. F. Bloom, Erdős Problems, Problem #537,
https://www.erdosproblems.com/537 (status DISPROVED (LEAN)); resolution: I. Z. Ruzsa's construction,
described by Erdős (argument on erdosproblems.com/537), erdosproblems.com/537: squarefree p₁ ⋯ p_r
with p_{i+1} > 2 p_i have positive density; their elements in (N/2, N) give a counterexample,
https://www.erdosproblems.com/537.
-/
public theorem_wanted denseSetHasPrimeMultipleTriple_refuted : ¬ denseSetHasPrimeMultipleTriple

end MathlibExt.NumberTheory.PrimeMultipleTripleDenseSetErdosProblem537Wanted
