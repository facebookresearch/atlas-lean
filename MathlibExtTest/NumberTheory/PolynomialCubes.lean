/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PolynomialCubes
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Int.Cast.Lemmas

/-! # Tests for `MathlibExt.NumberTheory.PolynomialCubes` -/

namespace MathlibExtTest.PolynomialCubes

open Polynomial MathlibExt.NumberTheory.PolynomialCubesWanted

-- At p = q = 0 the four cubes cancel, with every witness distinct from every constant.
example : ∃ f g h k : ℤ[X], (∀ c : ℤ, f ≠ C c ∧ g ≠ C c ∧ h ≠ C c ∧ k ≠ C c) ∧
    f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 = 0 := by
  obtain ⟨f, g, h, k, hf, hg, hh, hk, hsum⟩ :=
    int_sum_four_polynomial_cubes_of_cube_form 0 0 0 (Or.inl (by decide))
  refine ⟨f, g, h, k, ?_, by simpa using hsum⟩
  intro c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all

-- With p = 0, two slopes in (2.2) vanish. Four nonconstant witnesses still give the
-- required sum at every integer input.
example (q : ℤ) : ∃ f g h k : ℤ[X],
    1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧ 1 ≤ k.natDegree ∧
      ∀ t : ℤ, f.eval t ^ 3 + g.eval t ^ 3 + h.eval t ^ 3 + k.eval t ^ 3 = -2 * q ^ 6 := by
  obtain ⟨f, g, h, k, hf, hg, hh, hk, hsum⟩ :=
    int_sum_four_polynomial_cubes_of_cube_form (-2 * q ^ 6) 0 q (Or.inr (by simp))
  exact ⟨f, g, h, k, hf, hg, hh, hk, fun t ↦ by simpa using congrArg (eval t) hsum⟩

-- Test section: specialization. Evaluating the identity at any integer `t` writes `N` as a sum of
-- five cubes of integers, so every integer is a sum of five integer cubes.
example (N t : ℤ) : ∃ a b c d e : ℤ, a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 + e ^ 3 = N := by
  obtain ⟨f, g, h, k, l, -, -, -, -, -, hsum⟩ := int_eq_sum_five_polynomial_cubes N
  exact ⟨f.eval t, g.eval t, h.eval t, k.eval t, l.eval t, by simpa using congrArg (eval t) hsum⟩

-- Edge case: for `N = 0` the five cubes cancel, yet the degree bounds rule out the zero
-- polynomial, so none of the five polynomials is `0`.
example : ∃ f g h k l : ℤ[X], f ≠ 0 ∧ g ≠ 0 ∧ h ≠ 0 ∧ k ≠ 0 ∧ l ≠ 0 ∧
    f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 + l ^ 3 = 0 := by
  obtain ⟨f, g, h, k, l, hf, hg, hh, hk, hl, hsum⟩ := int_eq_sum_five_polynomial_cubes 0
  refine ⟨f, g, h, k, l, ?_, ?_, ?_, ?_, ?_, by simpa using hsum⟩ <;> rintro rfl <;> simp_all

-- Base change: over a ring of characteristic zero the integer cast is injective, so mapping the
-- five polynomials keeps them nonconstant and writes `N` as a sum of five cubes there too.
example {R : Type*} [CommRing R] [CharZero R] (N : ℤ) :
    ∃ f g h k l : R[X], 1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧
      1 ≤ k.natDegree ∧ 1 ≤ l.natDegree ∧
      f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 + l ^ 3 = C (N : R) := by
  obtain ⟨f, g, h, k, l, hf, hg, hh, hk, hl, hsum⟩ := int_eq_sum_five_polynomial_cubes N
  have hinj : Function.Injective (Int.castRingHom R) := Int.cast_injective
  refine ⟨f.map (Int.castRingHom R), g.map (Int.castRingHom R), h.map (Int.castRingHom R),
    k.map (Int.castRingHom R), l.map (Int.castRingHom R), ?_⟩
  simp only [natDegree_map_eq_of_injective hinj]
  refine ⟨hf, hg, hh, hk, hl, ?_⟩
  simpa [Polynomial.map_add, Polynomial.map_pow] using congrArg (map (Int.castRingHom R)) hsum

end MathlibExtTest.PolynomialCubes
