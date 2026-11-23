/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A thin additive complement of the powers of two (Erdős Problem 221)

Erdős Problem 221: is there `A ⊆ ℕ` with `|A ∩ {1, …, N}| ≪ N / log N` for all large `N` such that
every large integer is `2^k + a` with `k ≥ 0` and `a ∈ A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.PowersOfTwoAdditiveComplementErdosProblem221Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #221, https://www.erdosproblems.com/221 (status PROVED
(LEAN)). UnsolvedMath record UM-30006774 (`EP-221`), dataset ulamai/UnsolvedMath v1.8.0.

`≪ N / log N` is a constant `C` with `|A ∩ [1, N]| ≤ C N / log N` for all large `N`. Compared with
the formal-conjectures statement `ErdosProblems/221.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 221: there is `A ⊆ ℕ` with `|A ∩ [1, N]| ≪ N / log N` for all large `N` such
that every large integer is `2^k + a` with `k ≥ 0` and `a ∈ A`. -/
def thinComplementOfPowersOfTwo : Prop :=
  ∃ A : Set ℕ, (∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * N / Real.log N) ∧
    ∀ᶠ n : ℕ in Filter.atTop, ∃ k : ℕ, ∃ a ∈ A, n = 2 ^ k + a

/--
Resolved true: Ruzsa's set `A = {5ⁿ m : m ≥ 1, 5ⁿ ≥ C log m} + {0, 1}` has `|A ∩ [1, N]| ≪ N / log
N`, and every large integer is `2^k + a` with `a ∈ A` because `2` is a primitive root modulo every
`5ⁿ`; erdosproblems.com/221 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #221, https://www.erdosproblems.com/221 (status PROVED (LEAN)); resolution: I. Z. Ruzsa, On
a problem of P. Erdős, Canad. Math. Bull. 15 (1972), 309-310, erdosproblems.com/221: proved by Ruzsa
with A = {5^n m : m ≥ 1, 5^n ≥ C log m} + {0, 1}, https://doi.org/10.4153/CMB-1972-058-2.
-/
public theorem_wanted thinComplementOfPowersOfTwo_holds : thinComplementOfPowersOfTwo

end MathlibExt.NumberTheory.PowersOfTwoAdditiveComplementErdosProblem221Wanted
