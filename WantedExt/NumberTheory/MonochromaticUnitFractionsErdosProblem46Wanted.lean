/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic Egyptian fractions for 1 (Erdős Problem 46)

Erdős Problem 46: does every finite colouring of the integers have a monochromatic solution of `1 =
∑ 1/nᵢ` with `2 ≤ n₁ < ⋯ < n_k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.MonochromaticUnitFractionsErdosProblem46Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #46, https://www.erdosproblems.com/46 (status PROVED
(LEAN)). UnsolvedMath record UM-30006695 (`EP-46`), dataset ulamai/UnsolvedMath v1.8.0.

Colourings are maps `ℕ → Fin r`; only their values at integers `≥ 2` matter. Compared with the
formal-conjectures statement `ErdosProblems/46.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 46: every colouring of the integers `≥ 2` with finitely many colours has a
monochromatic solution of `1 = 1/n₁ + ⋯ + 1/n_k` with `2 ≤ n₁ < ⋯ < n_k`. -/
def colouringUnitFractionSum : Prop :=
  ∀ r : ℕ, ∀ c : ℕ → Fin r, ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧
    (∃ i : Fin r, ∀ n ∈ S, c n = i) ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

/--
Resolved true: Croot proved that every finite colouring of the integers `≥ 2` has a monochromatic
solution of `1 = ∑ 1/nᵢ` with distinct `nᵢ`, indeed infinitely many disjoint ones;
erdosproblems.com/46 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #46,
https://www.erdosproblems.com/46 (status PROVED (LEAN)); resolution: E. S. Croot III, On a coloring
conjecture about unit fractions, Ann. of Math. (2) (2003), 545-556, erdosproblems.com/46: yes, as
proved by Croot; indeed infinitely many disjoint solutions.
-/
public theorem_wanted colouringUnitFractionSum_holds : colouringUnitFractionSum

end MathlibExt.NumberTheory.MonochromaticUnitFractionsErdosProblem46Wanted
