/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Approximation.ChebyshevMinimax

@[expose] public section

open Polynomial Polynomial.Chebyshev MathlibExt.Analysis.Approximation.ChebyshevMinimax

namespace MathlibExtTest.Analysis.Approximation.ChebyshevMinimax

/-- Concrete: `2^{-1} T_2 = X^2 - 1/2`. -/
example : chebyshevMonic 2 = X ^ 2 - Polynomial.C (1 / 2 : ℝ) := by
  have hT : T ℝ (2 : ℕ) = 2 * X ^ 2 - 1 := by simpa using T_two (R := ℝ)
  rw [chebyshevMonic, hT]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [mul_sub, ← mul_assoc, show (2 : ℝ[X]) = Polynomial.C 2 from rfl, ← Polynomial.C_mul]
  norm_num

/-- Boundary `n = 0`: the bound is `1`, attained by the monic polynomial `1`. -/
example : ((2 : ℝ) ^ (0 - 1))⁻¹ = 1 := by norm_num

/-- The minimax bound applied to `X^2`: its sup norm `1` on `[-1, 1]` is at least `1/2`. -/
example : ((2 : ℝ) ^ (2 - 1))⁻¹ ≤ 1 :=
  inv_two_pow_le_of_forall_abs_eval_le (p := X ^ 2) (monic_X_pow 2) (natDegree_X_pow 2)
    (fun x hx => by
      have : |x| ≤ 1 := abs_le.2 hx
      simp only [eval_pow, eval_X, abs_pow]
      exact pow_le_one₀ (abs_nonneg x) this)

/-- A monic linear polynomial `X + c` has maximum modulus at least `1` on `[-1, 1]`. -/
example (c M : ℝ) (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(X + Polynomial.C c).eval x| ≤ M) :
    1 ≤ M := by
  have := inv_two_pow_le_of_forall_abs_eval_le (monic_X_add_C c) (natDegree_X_add_C c) hM
  simpa using this

/-- Equality case: a monic quadratic bounded by `1/2` on `[-1, 1]` is `X^2 - 1/2`. -/
example (p : ℝ[X]) (hp : p.Monic) (hdeg : p.natDegree = 2)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 / 2) : p = chebyshevMonic 2 :=
  eq_chebyshevMonic_of_forall_abs_eval_le hp hdeg (by simpa using hM)

end MathlibExtTest.Analysis.Approximation.ChebyshevMinimax
