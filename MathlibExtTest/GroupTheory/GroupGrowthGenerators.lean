/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupGrowthGenerators

@[expose] public section

namespace MathlibExtTest.GroupGrowthGenerators

open Group.Generators

/-- Every finite generating family of the infinite group `Multiplicative ℤ` has polynomial
growth. -/
example {ι : Type*} [Finite ι] (P : Group.Generators (Multiplicative ℤ) ι) :
    P.HasPolynomialGrowth :=
  HasPolynomialGrowth.of_generators P hasPolynomialGrowth_intGenerators

example {ι : Type*} [Finite ι] (P : Group.Generators (Multiplicative ℤ) ι) :
    P.HasPolynomialGrowth ↔ intGenerators.HasPolynomialGrowth :=
  hasPolynomialGrowth_iff P intGenerators

theorem wordLength_eq (x : Multiplicative ℤ) :
    intGenerators.wordLength x = (Multiplicative.toAdd x).natAbs := by
  rw [← wordLength_intGenerators, ofAdd_toAdd]

/-- Quasi-isometry invariance applied to the squaring map `g ↦ g ^ 2` of `Multiplicative ℤ`
(`n ↦ 2n` additively), a `(2, 0)`-quasi-isometric embedding which is not coarsely surjective. -/
example : intGenerators.HasPolynomialGrowth := by
  refine HasPolynomialGrowth.of_quasiIsometricEmbedding intGenerators intGenerators
    (fun g => g ^ 2) (L := 2) (C := 0) (fun g g' => ?_) (fun g g' => ?_)
    hasPolynomialGrowth_intGenerators
  · simp only [wordLength_eq, toAdd_mul, toAdd_inv, toAdd_pow, add_zero]
    have : (-Multiplicative.toAdd g + Multiplicative.toAdd g').natAbs ≤
        2 * (-(2 * Multiplicative.toAdd g) + 2 * Multiplicative.toAdd g').natAbs := by omega
    exact_mod_cast this
  · simp only [wordLength_eq, toAdd_mul, toAdd_inv, toAdd_pow, add_zero]
    have : (-(2 * Multiplicative.toAdd g) + 2 * Multiplicative.toAdd g').natAbs ≤
        2 * (-Multiplicative.toAdd g + Multiplicative.toAdd g').natAbs := by omega
    exact_mod_cast this

end MathlibExtTest.GroupGrowthGenerators
