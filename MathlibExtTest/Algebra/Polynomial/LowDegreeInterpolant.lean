/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
import MathlibExt.Algebra.Polynomial.LowDegreeInterpolant
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp

/-! # Tests for the integrality of low-degree interpolants -/

open MetaMathlibExt Polynomial

/-- The binomial polynomial `x (x - 1) / 2` does not have integer coefficients. -/
private theorem half_mul_X_mul_X_sub_one_notMem_lifts :
    C (1 / 2 : ℚ) * (X * (X - 1)) ∉ Polynomial.lifts (Int.castRingHom ℚ) := by
  rw [lifts_iff_coeff_lifts]
  intro h
  obtain ⟨n, hn⟩ := h 2
  have hcoeff : (C (1 / 2 : ℚ) * (X * (X - 1))).coeff 2 = 1 / 2 := by
    rw [coeff_C_mul, mul_sub, mul_one, ← pow_two, coeff_sub, coeff_X_pow_self, coeff_X]
    norm_num
  rw [hcoeff, eq_intCast] at hn
  field_simp at hn
  norm_cast at hn
  omega

-- The interpolation polynomial of an integer polynomial function has integer coefficients.
example (S : Finset ℤ) (p : ℤ[X]) :
    interpolationPoly S (fun z => p.eval z) ∈ Polynomial.lifts (Int.castRingHom ℚ) :=
  mem_lifts_of_degree_lt_of_eval_eq S _ (degree_interpolationPoly_lt S _) p
    fun _ hx => eval_interpolationPoly _ hx

-- No integer polynomial takes the values `0, 0, 1` at `0, 1, 2`: it would agree on three points
-- with `x (x - 1) / 2`, which has degree `2 < 3` and is not an integer polynomial.
example (p : ℤ[X]) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) : p.eval 2 ≠ 1 := by
  intro h2
  refine half_mul_X_mul_X_sub_one_notMem_lifts
    (mem_lifts_of_degree_lt_of_eval_eq {0, 1, 2} _ ?_ p ?_)
  · have hle : (C (1 / 2 : ℚ) * (X * (X - 1))).degree ≤ 2 := by compute_degree
    exact hle.trans_lt (by decide)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num [h0, h1, h2]

-- The degree bound is sharp: `x (x - 1) / 2` has degree `2 = |{0, 1}|` and agrees on `{0, 1}`
-- with the zero polynomial, but it is not an integer polynomial.
example : ∃ (S : Finset ℤ) (q : ℚ[X]) (p : ℤ[X]), q.degree = S.card ∧
    (∀ x ∈ S, q.eval (x : ℚ) = ((p.eval x : ℤ) : ℚ)) ∧
    q ∉ Polynomial.lifts (Int.castRingHom ℚ) := by
  refine ⟨{0, 1}, C (1 / 2 : ℚ) * (X * (X - 1)), 0, ?_, ?_,
    half_mul_X_mul_X_sub_one_notMem_lifts⟩
  · have hdeg : (C (1 / 2 : ℚ) * (X * (X - 1))).degree = 2 := by compute_degree!
    rw [hdeg]
    rfl
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
