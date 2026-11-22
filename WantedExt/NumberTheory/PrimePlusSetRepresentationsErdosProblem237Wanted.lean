/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Representations as a prime plus an element of a sparse set (Erdős Problem 237)

Erdős Problem 237: let `A ⊆ ℕ` satisfy `|A ∩ {1, …, N}| ≫ log N` for all large `N`, and let `f(n)`
count the solutions of `n = p + a` with `p` prime and `a ∈ A`. Is `limsup f(n) = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.PrimePlusSetRepresentationsErdosProblem237Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #237, https://www.erdosproblems.com/237 (status PROVED
(LEAN)). UnsolvedMath record UM-30006786 (`EP-237`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ log N` is `|A ∩ [1, N]| ≥ c log N` for some `c > 0` and all large `N`; `limsup f(n) = ∞` is "for
every `M`, `f(n) ≥ M` for infinitely many `n`". Compared with the formal-conjectures statement
`ErdosProblems/237.lean` (equivalent; no code imported).
-/

open Filter

/-- The number `f(n)` of representations `n = p + a` with `p` prime and `a ∈ A`. -/
noncomputable def primePlusCount (A : Set ℕ) (n : ℕ) : ℕ :=
  {a ∈ A | a ≤ n ∧ (n - a).Prime}.ncard

/-- Erdős Problem 237: if `A ⊆ ℕ` satisfies `|A ∩ [1, N]| ≥ c log N` for some `c > 0` and all large
`N`, then the number `f(n)` of representations `n = p + a` (`p` prime, `a ∈ A`) satisfies
`limsup f(n) = ∞`. -/
def primePlusSetRepresentationsUnbounded : Prop :=
  ∀ A : Set ℕ, (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ (A ∩ Set.Icc 1 N).ncard) →
    ∀ M : ℕ, ∃ᶠ n in atTop, M ≤ primePlusCount A n

/--
Resolved true: Chen and Ding proved (Corollary 1.3) that `limsup f(n) = ∞` for every infinite `A ⊆
ℕ`, so the density hypothesis is not needed; erdosproblems.com/237 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #237, https://www.erdosproblems.com/237 (status PROVED
(LEAN)); resolution: Y.-G. Chen and Y. Ding, On a conjecture of Erdős, arXiv:2201.10727 (2022),
Corollary 1.3: limsup f_A(n) = +∞ for every infinite set A of integers (from Theorem 1.1 via the
Maynard-Tao theorem); erdosproblems.com/237, https://arxiv.org/abs/2201.10727.
-/
public theorem_wanted primePlusSetRepresentationsUnbounded_holds :
    primePlusSetRepresentationsUnbounded

end MathlibExt.NumberTheory.PrimePlusSetRepresentationsErdosProblem237Wanted
