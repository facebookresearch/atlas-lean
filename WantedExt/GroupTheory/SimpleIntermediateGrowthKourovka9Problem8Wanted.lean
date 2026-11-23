/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated simple groups of intermediate growth (Kourovka Notebook Problem 9.8)

Kourovka Notebook, Archive of Solved Problems, Problem 9.8 (R. I. Grigorchuk): does there exist a
finitely generated simple group of intermediate growth?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Simple
public import MathlibExt.GroupTheory.GroupGrowth

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleIntermediateGrowthKourovka9Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.8 (R. I.
Grigorchuk). UnsolvedMath record UM-00700543 (`KOU-9.8`), dataset ulamai/UnsolvedMath v1.8.0.

Growth is MathlibExt's `Group.Generators.growth` (size of the word ball of radius `n`) for a finite
generating family. Intermediate growth: not bounded by a polynomial (`¬ HasPolynomialGrowth`) and
subexponential (eventually at most `cⁿ` for every `c > 1`); both properties do not depend on the
finite generating family.
-/

/-- Kourovka 9.8 (R. I. Grigorchuk): there is a finitely generated simple group of intermediate
growth: for a finite generating family `P` the growth function `n ↦ |B(n)|` (MathlibExt
`Group.Generators.growth`) is not bounded by a polynomial and is subexponential (eventually below
`cⁿ` for every `c > 1`). -/
def existsSimpleIntermediateGrowth : Prop :=
  ∃ (G : Type) (_ : Group G) (ι : Type) (_ : Finite ι) (P : Group.Generators G ι),
    IsSimpleGroup G ∧ ¬ P.HasPolynomialGrowth ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ n in Filter.atTop, (P.growth n : ℝ) ≤ c ^ n

/--
Resolved true: Nekrashevych gives the first examples of finitely generated simple groups of
intermediate growth (simple periodic groups from palindromic subshifts); the Kourovka Archive
answers 9.8 "Yes, it does". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 9.8 (R. I. Grigorchuk); resolution: V. Nekrashevych, Palindromic subshifts and
simple periodic groups of intermediate growth, Ann. of Math. 187 (2018), no. 3, 667-719, abstract:
finitely generated periodic groups built from minimal actions of the dihedral group on a Cantor set
are of intermediate growth when the Schreier graphs are linearly repetitive, giving the first
examples of simple groups of intermediate growth; Kourovka Archive of Solved Problems, Problem 9.8:
Yes, it does, https://doi.org/10.4007/annals.2018.187.3.2.
-/
public theorem_wanted existsSimpleIntermediateGrowth_holds : existsSimpleIntermediateGrowth

end MathlibExt.GroupTheory.SimpleIntermediateGrowthKourovka9Problem8Wanted
