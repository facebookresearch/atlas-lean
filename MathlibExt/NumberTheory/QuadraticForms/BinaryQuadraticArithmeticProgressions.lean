/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Rat.Defs
import Mathlib.Basic.Finite.Sum
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Rational and integral representations by binary quadratic forms

A common denominator for both coordinates of every representation scales a finite
arithmetic progression by its square. The ATLAS wiki attributes this result to Ajai
Choudhry's “Arithmetic Progressions Represented by Binary Quadratic Forms”.
-/

public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- If an integral binary quadratic form represents each term of a finite arithmetic
progression over the rationals, then it represents every term over the integers after
multiplying the progression by a single nonzero integer square. -/
theorem exists_int_representations_of_rat_arithmetic_progression
    (a b c : ℤ) (n : ℕ) (u0 d : ℚ)
    (hrep : ∀ i ∈ Finset.range n, ∃ x y : ℚ,
      (a : ℚ) * x ^ 2 + (b : ℚ) * x * y + (c : ℚ) * y ^ 2 =
        u0 + i * d) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range n, ∃ x y : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2 : ℚ) =
        (k : ℚ) ^ 2 * (u0 + i * d) := by
  choose x y hxy using fun i : Fin n => hrep i (Finset.mem_range.mpr i.isLt)
  -- Index both families of coordinates together to clear all denominators at once.
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Sum.elim x y)
  refine ⟨k, nonZeroDivisors.coe_ne_zero k, ?_⟩
  intro i hi
  let j : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨X, hX⟩ := hk (Sum.inl j)
  obtain ⟨Y, hY⟩ := hk (Sum.inr j)
  refine ⟨X, Y, ?_⟩
  simp only [eq_intCast, zsmul_eq_mul, Sum.elim_inl, Sum.elim_inr] at hX hY
  rw [hX, hY, ← hxy j]
  ring

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted
