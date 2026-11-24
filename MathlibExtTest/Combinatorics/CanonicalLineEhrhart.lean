/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CanonicalLineEhrhart
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

open Polynomial MetaMathlibExt

-- A negative real scale is allowed, including for a polynomial of degree zero.
example : IsCLWithParameters (C (-1 : ℂ)) (-1) [] := by
  simp [IsCLWithParameters, clQuadraticProduct]

-- For a single quadratic factor the parameter bound includes its endpoint.
example (c : ℝ) : IsCLWithParameters (X ^ 2 + X + C (c : ℂ)) 1 [c] ↔ 1 / 4 ≤ c := by
  have hd : (X ^ 2 + X + C (c : ℂ)).natDegree = 2 := by compute_degree!
  simp [IsCLWithParameters, clQuadraticProduct, hd]

-- The odd linear factor takes purely imaginary values at every height on the line.
example (t : ℝ) : ((2 * X + 1 : Polynomial ℂ).eval ⟨-(1 / 2), t⟩).re = 0 := by
  have hd : (2 * X + 1 : Polynomial ℂ).natDegree = 1 := by compute_degree!
  have hf : IsCL (2 * X + 1) :=
    ⟨1, [], by simp [IsCLWithParameters, clQuadraticProduct, hd]⟩
  obtain ⟨r, hr⟩ := cl_value_on_canonicalLine _ hf ⟨-(1 / 2), t⟩ rfl
  rw [hr, hd, pow_one]
  simp

-- At j = 0 and c = 0, the coefficient of the highest shift vanishes.
example : (X ^ 2 + X) * binomialPolynomial 1 1 =
    C 4 * binomialPolynomial 2 3 + C 2 * binomialPolynomial 1 3 := by
  have h := quadratic_mul_binomialPolynomial 1 0 (by decide) (by decide) 0
  norm_num at h
  exact h

-- At j = d the base shift is zero, and with c = 0 the last term vanishes.
example : (X ^ 2 + X) * binomialPolynomial 0 1 =
    C 2 * binomialPolynomial 2 3 + C 4 * binomialPolynomial 1 3 := by
  have h := quadratic_mul_binomialPolynomial 1 1 (by decide) (by decide) 0
  norm_num at h
  exact h

-- All three terms survive in this interior case, even with c below 1/4.
example : (X ^ 2 + X + C (-1)) * binomialPolynomial 2 3 =
    binomialPolynomial 4 5 + C 14 * binomialPolynomial 3 5 +
      C 5 * binomialPolynomial 2 5 := by
  have h := quadratic_mul_binomialPolynomial 3 1 (by decide) (by decide) (-1)
  norm_num at h ⊢
  exact h

-- The degree-zero case uses only the constant h-star coefficient of the input.
example : IsSNN ((2 * X + 1) * (1 : Polynomial ℂ)) := by
  apply two_mul_X_add_one_preserves_snn
  refine ⟨one_ne_zero, ?_⟩
  intro i hi
  have : i = 0 := Nat.eq_zero_of_le_zero (by simpa using hi)
  subst i
  simp [hStarCoeff]

-- X has h-star coefficients 0 and 1, so the highest output coefficient need not vanish.
example : IsSNN ((2 * X + 1) * (X : Polynomial ℂ)) := by
  apply two_mul_X_add_one_preserves_snn
  refine ⟨X_ne_zero, ?_⟩
  intro i hi
  have hi' : i ≤ 1 := by simpa using hi
  rcases i with _ | (_ | i)
  · simp [hStarCoeff]
  · norm_num [hStarCoeff, Finset.sum_range_succ, Nat.choose]
  · omega

example : hStarCoeff ((2 * X + 1) * (X : Polynomial ℂ))
    (((2 * X + 1) * (X : Polynomial ℂ)).natDegree) = 1 := by
  have hd : ((2 * X + 1) * (X : Polynomial ℂ)).natDegree = 2 := by compute_degree!
  rw [hd]
  norm_num [hStarCoeff, hd, Finset.sum_range_succ, Nat.choose]

#print axioms MetaMathlibExt.binomialPolynomial
#print axioms MetaMathlibExt.quadratic_mul_binomialPolynomial
#print axioms MetaMathlibExt.two_mul_X_add_one_preserves_snn
