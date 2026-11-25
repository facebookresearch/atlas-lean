/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.HadamardProductRational
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace MetaMathlibExt.HadamardProductRationalTest

open PowerSeries

-- With no denominator factors, the coefficientwise product of polynomials is a polynomial.
example (R S : Polynomial ℚ) :
    ∃ T : Polynomial ℚ, mk (fun k ↦ R.coeff k * S.coeff k) = (T : PowerSeries ℚ) := by
  simpa using (hadamardProduct_rational 0 0 Fin.elim0 Fin.elim0 R S R S (by simp) (by simp)).1

-- A repeated factor in the first denominator appears twice in the product denominator.
example (a b : ℚ) (A B : PowerSeries ℚ) (R S : Polynomial ℚ)
    (hA : A * (1 - C a * X) ^ 2 = (R : PowerSeries ℚ))
    (hB : B * (1 - C b * X) = (S : PowerSeries ℚ)) :
    ∃ T : Polynomial ℚ, mk (fun k ↦ coeff k A * coeff k B) * (1 - C (a * b) * X) ^ 2 =
      (T : PowerSeries ℚ) := by
  simpa [Fin.prod_univ_two, pow_two] using
    (hadamardProduct_rational 2 1 (fun _ ↦ a) (fun _ ↦ b) R S A B
      (by simpa [Fin.prod_univ_two, pow_two] using hA) (by simpa using hB)).1

-- Padding a geometric denominator with a zero parameter still gives a proper product.
example : ∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
    mk (fun k ↦ coeff k (mk (1 : ℕ → ℚ)) * coeff k (mk (1 : ℕ → ℚ))) *
      (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  let g := mk (1 : ℕ → ℚ)
  have hg : g * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℚ
  have hp : ∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
      g * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
    refine ⟨1, 1 - Polynomial.X, by simp, ?_, by simpa using hg⟩
    rw [Polynomial.degree_sub_eq_right_of_degree_lt (by simp), Polynomial.degree_X]
    simp
  exact (hadamardProduct_rational 2 1 (fun i ↦ if i = 0 then 0 else 1) (fun _ ↦ 1)
    1 1 g g (by simpa [Fin.prod_univ_two] using hg) (by simpa using hg)).2 hp hp

end MetaMathlibExt.HadamardProductRationalTest
