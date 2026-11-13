/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic solutions of `1/a = 1/b + 1/c` (Erdős Problem 303)

Erdős Problem 303: in any finite colouring of the integers, is there a monochromatic solution of
`1/a = 1/b + 1/c` with distinct `a, b, c`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Init

@[expose] public section

namespace MathlibExt.NumberTheory.MonochromaticUnitFractionErdosProblem303Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #303, https://www.erdosproblems.com/303 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 37. UnsolvedMath record UM-30006816 (`EP-303`), dataset ulamai/UnsolvedMath v1.8.0.

The integers are the positive integers (a colouring of `ℕ` restricted to `n ≥ 1`), as in Brown and
Rödl; formal-conjectures `ErdosProblems/303.lean` colours `ℤ` and allows nonzero solutions of either
sign, a weaker form implied by this one (no code imported).
-/

/-- Erdős Problem 303: in every colouring of the positive integers with finitely many (`k`)
colours there are distinct positive integers `a, b, c` of one colour with `1/a = 1/b + 1/c`. -/
def monochromaticUnitFractionTriple : Prop :=
  ∀ (k : ℕ) (colour : ℕ → Fin k), ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    colour a = colour b ∧ colour a = colour c ∧ (1 : ℚ) / a = 1 / b + 1 / c

/--
Resolved true: Brown and Rödl proved that every finite colouring of the positive integers has a
monochromatic solution of `1/a = 1/b + 1/c` with `a, b, c` distinct. erdosproblems.com/303 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #303,
https://www.erdosproblems.com/303 (status PROVED (LEAN)); P. Erdős and R. L. Graham, Old and new
problems and results in combinatorial number theory (1980), p. 37; resolution: T. C. Brown and V.
Rödl, Monochromatic solutions to equations with unit fractions, Bull. Austral. Math. Soc. (1991),
387-392, erdosproblems.com/303: the colouring version is true, as proved by Brown and Rödl,
https://www.erdosproblems.com/303.
-/
public theorem_wanted monochromaticUnitFractionTriple_holds : monochromaticUnitFractionTriple

end MathlibExt.NumberTheory.MonochromaticUnitFractionErdosProblem303Wanted
