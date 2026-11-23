/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The square-root suborder test adapts the coordinate argument of lines
216–252 of `P2M/Sol/S_fermatLastTheoremFive.lean`,
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib, copyright its respective authors,
released under the Apache License, Version 2.0. No individual authors are
identified for this source file in the upstream ATTRIBUTION.md.
-/
module

public import MathlibExtTest.NumberTheory.QuadraticForms.GoldenOrderSource
public import Mathlib.Algebra.Order.Star.Real

public section

namespace GoldenOrderTest

open QuadraticAlgebra

/-- Pull the canonical real Fibonacci formula back to integral coordinates. -/
theorem fibonacci_coordinates (n : ℕ) :
    (omega : QuadraticAlgebra ℤ 1 1) ^ (n + 1) =
      ⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ := by
  apply goldenEquiv.injective
  apply Subtype.ext
  simpa [mul_comm, add_comm] using
    (Real.goldenRatio_mul_fib_succ_add_fib n).symm

/-- A Pell norm identity obtained from the transported Fibonacci coordinates. -/
theorem fibonacci_pell_norm (n : ℕ) :
    (Nat.fib n : ℤ) ^ 2 + (Nat.fib n : ℤ) * Nat.fib (n + 1) -
      (Nat.fib (n + 1) : ℤ) ^ 2 = (-1 : ℤ) ^ (n + 1) := by
  have h := congrArg (fun z : QuadraticAlgebra ℤ 1 1 => norm z)
    (fibonacci_coordinates n)
  rw [map_pow] at h
  simpa [norm_def, pow_two] using h.symm

namespace Source

open GoldenOrderSource.Zphi

/-- The source's actual generator evaluates to the positive golden ratio. -/
theorem phi_value : (goldenEquiv (coordinateEquiv phi) : ℝ) =
    Real.goldenRatio := by simp

/-- Every source coordinate is preserved before real evaluation. -/
theorem coordinate_value (z : GoldenOrderSource.Zphi) :
    (goldenEquiv (coordinateEquiv z) : ℝ) =
      z.re + z.im * Real.goldenRatio := by
  simp [coordinateEquiv]

-- The source carrier must never be silently replaced by a definitional alias.
example : True := by
  fail_if_success
    have : GoldenOrderSource.Zphi = QuadraticAlgebra ℤ 1 1 := rfl
  trivial

/-- The actual source generator and its inverse, including norm -1. -/
theorem generator_inverse : phi * (phi - 1) = 1 ∧
    GoldenOrderSource.Zphi.norm phi = -1 ∧
      GoldenOrderSource.Zphi.norm (phi - 1) = -1 := by
  constructor
  · ext <;> simp
  · simp [GoldenOrderSource.Zphi.norm]

/-- Negative exponents become the third and fourth source cases. -/
theorem signed_inverse_powers (n : ℕ) :
    (phi - 1) ^ n * phi ^ n = 1 ∧
      (-((phi - 1) ^ n)) * phi ^ n = -1 := by
  have h : (phi - 1) * phi = 1 := by
    rw [mul_comm]
    exact generator_inverse.1
  constructor
  · rw [← mul_pow, h, one_pow]
  · rw [neg_mul, ← mul_pow, h, one_pow]

/-- Source conjugation is not real star, already on the source generator. -/
theorem conjugation_not_real_star :
    (goldenEquiv (coordinateEquiv (conj phi)) : ℝ) ≠
      star (goldenEquiv (coordinateEquiv phi) : ℝ) := by
  rw [coordinateEquiv_conj, coordinateEquiv_phi, coe_goldenEquiv_star]
  simp only [coe_goldenEquiv, re_omega, im_omega, Int.cast_zero,
    Int.cast_one, one_mul, zero_add, star_trivial]
  linarith [Real.one_lt_goldenRatio]

/-- The source F216 `ofPair` image has precisely even imaginary coordinate. -/
theorem sqrt5_suborder (z : GoldenOrderSource.Zphi) :
    (∃ a b : ℤ, z = ⟨a - b, 2 * b⟩) ↔ Even z.im := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨b, by simp; ring⟩
  · rintro ⟨b, hb⟩
    refine ⟨z.re + b, b, ?_⟩
    ext <;> simp
    omega

/-- In particular, the source generator is not in the square-root suborder. -/
theorem phi_not_sqrt5_suborder :
    ¬ ∃ a b : ℤ, phi = (⟨a - b, 2 * b⟩ : GoldenOrderSource.Zphi) := by
  rw [sqrt5_suborder]
  norm_num

/-- Norm zero and norm four are excluded by the canonical unit criterion. -/
theorem excluded_nonunits : ¬ IsUnit (0 : GoldenOrderSource.Zphi) ∧
    ¬ IsUnit (2 : GoldenOrderSource.Zphi) := by
  constructor <;> intro h
  · have hn := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
      (h.map coordinateEquiv)
    norm_num [Int.isUnit_iff] at hn
  · have hn := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
      (h.map coordinateEquiv)
    norm_num [Int.isUnit_iff, GoldenOrderSource.Zphi.norm] at hn

/-- All four source cases are inhabited by units, including inverse powers. -/
theorem units_at_signed_powers (n : ℕ) :
    IsUnit (phi ^ n) ∧ IsUnit (-(phi ^ n)) ∧
      IsUnit ((phi - 1) ^ n) ∧ IsUnit (-((phi - 1) ^ n)) := by
  have hinv : (phi - 1) * phi = 1 := by
    rw [mul_comm]
    exact generator_inverse.1
  have hp : IsUnit phi :=
    ⟨⟨phi, phi - 1, generator_inverse.1, hinv⟩, rfl⟩
  have hi : IsUnit (phi - 1) :=
    ⟨⟨phi - 1, phi, hinv, generator_inverse.1⟩, rfl⟩
  exact ⟨hp.pow n, (hp.pow n).neg, hi.pow n, (hi.pow n).neg⟩

/-- Concrete zero-exponent, positive, negative and signed coordinate boundaries. -/
theorem coordinate_boundaries :
    phi ^ 0 = 1 ∧ phi ^ 3 = ⟨1, 2⟩ ∧ -(phi ^ 3) = ⟨-1, -2⟩ ∧
      (phi - 1) ^ 3 = ⟨-3, 2⟩ ∧ -((phi - 1) ^ 3) = ⟨3, -2⟩ ∧
      conj phi = ⟨1, -1⟩ := by decide

/-- Norm transport refers to the actual source norm, not a fresh definition. -/
theorem source_norm_real (z : GoldenOrderSource.Zphi) :
    (GoldenOrderSource.Zphi.norm z : ℝ) =
      (z.re + z.im * Real.goldenRatio) *
        (z.re + z.im * (1 - Real.goldenRatio)) := by
  have h := norm_eq_goldenEquiv_mul (coordinateEquiv z)
  rw [coordinateEquiv_norm] at h
  simpa [coordinateEquiv] using h

example : (goldenEquiv (coordinateEquiv 0) : ℝ) = 0 := by simp
example : (goldenEquiv (coordinateEquiv (phi - 1)) : ℝ) =
    Real.goldenRatio ^ (-1 : ℤ) := by
  simp only [map_sub, coordinateEquiv_phi, map_one, Subalgebra.coe_sub,
    coe_goldenEquiv, re_omega, im_omega, Int.cast_zero, Int.cast_one,
    one_mul, zero_add, Subalgebra.coe_one, zpow_neg_one]
  rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
  ring

end Source
end GoldenOrderTest
