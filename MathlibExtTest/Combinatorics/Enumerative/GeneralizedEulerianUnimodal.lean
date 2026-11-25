/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedEulerianUnimodal
import Mathlib.Algebra.Polynomial.Roots

open MetaMathlibExt

-- The punctured evaluation condition determines even the value at the omitted point.
-- With zero cycle weight the unique witness is one in degree zero and zero thereafter.
example (t n : ℕ) :
    ∃ p : Polynomial ℚ, (∀ x : ℚ, x ≠ 1 → p.eval x = generalizedEulerianP 0 t x 1 n) ∧
      p = (if n = 0 then 1 else 0) := by
  obtain ⟨p, hp, _⟩ := generalizedEulerianP_unimodal 0 t n
  refine ⟨p, hp, Polynomial.eq_of_infinite_eval_eq _ _ ?_⟩
  apply (Set.finite_singleton (1 : ℚ)).infinite_compl.mono
  intro x hx
  change p.eval x = _
  rw [hp x hx, Nat.cast_zero, generalizedEulerianP_zero_left]
  split <;> simp

-- With unit weights, the first polynomial takes different values at zero and minus one.
example : ∃ (p : Polynomial ℚ) (m : ℕ), p.eval 0 = 1 ∧ p.eval (-1) = 0 ∧
    (∀ i < m, p.coeff i ≤ p.coeff (i + 1)) ∧
    ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i := by
  obtain ⟨p, hp, m, hm⟩ := generalizedEulerianP_unimodal 1 1 1
  refine ⟨p, m, ?_, ?_, hm⟩
  · rw [hp 0 (by norm_num)]
    have hu := PowerSeries.mul_inv_cancel (-1 : PowerSeries ℚ) (by simp)
    simp only [neg_one_mul] at hu
    simp [generalizedEulerianP, generalizedEulerianSeries, hu,
      PowerSeries.subst_zero_eq_C_constantCoeff]
  · exact (hp (-1) (by norm_num)).trans (generalizedEulerianP_neg_one 1 1 0).1
