/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets on which Euler's totient is increasing (Erdős Problem 49)

Erdős Problem 49: if `A = {a₁ < ⋯ < a_t} ⊆ {1, …, N}` has `φ(a₁) < ⋯ < φ(a_t)`, is `|A| < (1 + o(1))
π(N)`, or at least `|A| = o(N)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.TotientIncreasingSetErdosProblem49Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #49, https://www.erdosproblems.com/49 (status PROVED
(LEAN)). UnsolvedMath record UM-30006698 (`EP-49`), dataset ulamai/UnsolvedMath v1.8.0.

`(1 + o(1)) π(N)` is unfolded as "for every `ε > 0` and all large `N`, `|A| ≤ (1 + ε) π(N)`". It
implies `|A| = o(N)`. Whether the primes are exactly optimal is not part of the target. Compared
with the formal-conjectures statement `ErdosProblems/49.lean` (equivalent to `erdos_49`; it uses a
`sSup`; no code imported).
-/

/-- Erdős Problem 49: if `A ⊆ {1, …, N}` and `φ` is strictly increasing on `A`, then
`|A| ≤ (1 + o(1)) π(N)`. For every `ε > 0` and all large `N`, `|A| ≤ (1 + ε) π(N)`. -/
def totientStrictMonoSetCardBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    StrictMonoOn Nat.totient (A : Set ℕ) → (A.card : ℝ) ≤ (1 + ε) * Nat.primeCounting N

/--
Resolved true: Tao proved `|A| ≤ (1 + O((log log N) ^ 5 / log N)) π(N)` even when `φ` is only
nondecreasing on `A`. Source: T. F. Bloom, Erdős Problems, Problem #49,
https://www.erdosproblems.com/49 (status PROVED (LEAN)); resolution: T. Tao, Monotone nondecreasing
sequences of the Euler totient function, Matematica (2024), 793-820, arXiv:2309.02325 abstract: the
largest subset of {n ≤ x} on which φ is non-decreasing has (1 + O((log log x)^5 / log x)) π(x)
elements for all x ≥ 10; erdosproblems.com/49, https://arxiv.org/abs/2309.02325.
-/
public theorem_wanted totientStrictMonoSetCardBound_holds : totientStrictMonoSetCardBound

end MathlibExt.NumberTheory.TotientIncreasingSetErdosProblem49Wanted
