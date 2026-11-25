/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsDerangementPolynomial
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! # Tests for the real zeros of the derangement cycle polynomial -/

namespace MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutationsDerangementPolynomial

open MetaMathlibExt Polynomial

-- At the smallest allowed `n = 2`, the polynomial is `D₂(x) = d(3, 1) + d(4, 2) x`, where
-- `d(3, 1)` counts the 3-cycles of three points and `d(4, 2)` the products of two disjoint
-- transpositions of four points.
example : (C (kPermFixedPointCount 3 1 0 : ℝ) + C (kPermFixedPointCount 4 2 0 : ℝ) * X).Splits := by
  have h := derangementCyclePolynomial_real_roots (n := 2) le_rfl
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by decide)] at h
  simpa using h

-- For `n = 3`, `D₃(x) = d(4, 1) + d(5, 2) x + d(6, 3) x ^ 2`; a real zero of the quadratic forces
-- a nonnegative discriminant, so `4 d(4, 1) d(6, 3) ≤ d(5, 2) ^ 2`.
example : 4 * (kPermFixedPointCount 4 1 0 : ℝ) * kPermFixedPointCount 6 3 0 ≤
    (kPermFixedPointCount 5 2 0 : ℝ) ^ 2 := by
  have h := derangementCyclePolynomial_real_roots (n := 3) (by norm_num)
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)] at h
  simp only [Nat.reduceAdd, Nat.sub_self, Nat.add_one_sub_one, pow_zero, mul_one, pow_one] at h
  set a := (kPermFixedPointCount 4 1 0 : ℝ)
  set b := (kPermFixedPointCount 5 2 0 : ℝ)
  set c := (kPermFixedPointCount 6 3 0 : ℝ)
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, mul_zero]
    positivity
  · have hdeg : (C a + (C b * X + C c * X ^ 2)).degree ≠ 0 := by
      intro h0
      have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) (eq_C_of_degree_eq_zero h0)
      exact hc (by simpa [coeff_C, coeff_X] using h2)
    obtain ⟨x, hx⟩ := h.exists_eval_eq_zero hdeg
    have hq : c * (x * x) + b * x + a = 0 := by
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at hx
      linear_combination hx
    have hd := discrim_eq_sq_of_quadratic_eq_zero hq
    rw [discrim] at hd
    nlinarith [sq_nonneg (2 * c * x + b)]

-- `Splits` says that every zero is real: counted with multiplicity, `Dₙ` has as many real roots
-- as its degree.
example {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ[X] := ∑ k ∈ Finset.Icc 1 n, C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ (k - 1)
    Multiset.card D.roots = D.natDegree :=
  splits_iff_card_roots.mp (derangementCyclePolynomial_real_roots hn)

-- Equivalently, `Dₙ` is its leading coefficient times the product of `X - r` over its real roots.
example {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ[X] := ∑ k ∈ Finset.Icc 1 n, C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ (k - 1)
    C D.leadingCoeff * (D.roots.map fun r => X - C r).prod = D :=
  (derangementCyclePolynomial_real_roots hn).eq_prod_roots.symm

end MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutationsDerangementPolynomial
