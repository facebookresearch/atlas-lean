/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic unit fraction sums among divisors (Erdős Problem 45)

Erdős Problem 45: let `k ≥ 2`. Is there `n_k` such that, with `D = {1 < d < n_k : d ∣ n_k}`, every
`k`-colouring of `D` has a monochromatic `D' ⊆ D` with `∑_{d ∈ D'} 1/d = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Divisors

@[expose] public section

namespace MathlibExt.NumberTheory.MonochromaticDivisorUnitFractionsErdosProblem45Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #45, https://www.erdosproblems.com/45 (status PROVED
(LEAN)). UnsolvedMath record UM-30006694 (`EP-45`), dataset ulamai/UnsolvedMath v1.8.0.

Colourings of `D` are restrictions of maps `ℕ → Fin k`. Compared with the formal-conjectures
statement `ErdosProblems/45.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 45: for every `k ≥ 2` there is `n` such that every `k`-colouring of the divisors
`1 < d < n` of `n` has a monochromatic set `D` of such divisors with `∑_{d ∈ D} 1/d = 1`. -/
def divisorColouringUnitFractionSum : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ n : ℕ, ∀ c : ℕ → Fin k,
    ∃ D ⊆ n.divisors.filter fun d => 1 < d ∧ d < n,
      (∃ i : Fin k, ∀ d ∈ D, c d = i) ∧ ∑ d ∈ D, (1 : ℚ) / d = 1

/--
Resolved true: this follows from Croot's colouring theorem for unit fractions, with `n_k ≤ e^{C^k}`
(take `n_k = lcm(1, …, ⌊C^k⌋)`); erdosproblems.com/45 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #45, https://www.erdosproblems.com/45 (status PROVED (LEAN));
resolution: E. S. Croot III, On a coloring conjecture about unit fractions, Ann. of Math. (2)
(2003), 545-556, follows from Croot's colouring theorem, with n_k ≤ e^{C^k} (erdosproblems.com/45).
-/
public theorem_wanted divisorColouringUnitFractionSum_holds : divisorColouringUnitFractionSum

end MathlibExt.NumberTheory.MonochromaticDivisorUnitFractionsErdosProblem45Wanted
