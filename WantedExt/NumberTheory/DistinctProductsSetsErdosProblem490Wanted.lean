/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pairs of sets with distinct products (Erdős Problem 490)

Erdős Problem 490: if `A, B ⊆ {1, …, N}` and all products `a b` (`a ∈ A`, `b ∈ B`) are distinct, is
`|A| |B| ≪ N ^ 2 / log N`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctProductsSetsErdosProblem490Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #490, https://www.erdosproblems.com/490 (status PROVED
(LEAN)). UnsolvedMath record UM-30006897 (`EP-490`), dataset ulamai/UnsolvedMath v1.8.0.

`≪` is a single constant `C` for all `N ≥ 2` (equivalent to "for large `N`", since `|A| |B| ≤ N ^
2`). Erdős's later question on the limit of the normalized maximum appears in the page commentary,
not in the recorded problem. Compared with the formal-conjectures statement `ErdosProblems/490.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 490: there is `C` such that for all `N ≥ 2` and `A, B ⊆ {1, …, N}` whose products
`a b` (`a ∈ A`, `b ∈ B`) are pairwise distinct, `|A| |B| ≤ C N ^ 2 / log N`. -/
def distinctProductsCardBound : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
    (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B, a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
      (A.card * B.card : ℝ) ≤ C * N ^ 2 / Real.log N

/--
Resolved true: Szemerédi proved `|A| |B| ≪ N ^ 2 / log N`; the example `A = [1, N/2]`, `B` = primes
in `(N/2, N]` shows this is sharp up to the constant. Source: T. F. Bloom, Erdős Problems, Problem
#490, https://www.erdosproblems.com/490 (status PROVED (LEAN)); resolution: E. Szemerédi, On a
problem of P. Erdős, J. Number Theory (1976), 264-270, erdosproblems.com/490: true, proved by
Szemerédi, https://www.erdosproblems.com/490.
-/
public theorem_wanted distinctProductsCardBound_holds : distinctProductsCardBound

end MathlibExt.NumberTheory.DistinctProductsSetsErdosProblem490Wanted
