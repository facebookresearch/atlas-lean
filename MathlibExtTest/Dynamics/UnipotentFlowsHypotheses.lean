/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The hypotheses of Margulis's theorem on values of quadratic forms are satisfiable

The form `Q(x₀, x₁, x₂) = x₀² + x₁² - √2 x₂²` (cf. D. W. Morris, *Ratner's theorems on unipotent
flows*, arXiv:math/0310402, Example 1.2.3) is indefinite, nondegenerate and not a scalar multiple
of a form with integer coefficients, in exactly the sense of the hypotheses of the wanted theorem
`MathlibExt.Dynamics.UnipotentFlowsWanted.margulis_oppenheim`.
-/

namespace MathlibExtTest.Dynamics.UnipotentFlowsHypotheses

/-- The weights `(1, 1, -√2)`. -/
noncomputable def w : Fin 3 → ℝ := ![1, 1, -Real.sqrt 2]

/-- The quadratic form `x₀² + x₁² - √2 x₂²`. -/
noncomputable def Q : QuadraticForm ℝ (Fin 3 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ w

theorem Q_apply (x : Fin 3 → ℝ) : Q x = ∑ i, w i * (x i * x i) := by
  simp [Q, QuadraticMap.weightedSumSquares_apply]

theorem Q_single (i : Fin 3) : Q (Pi.single i 1) = w i := by
  rw [Q_apply]
  fin_cases i <;> simp [Fin.sum_univ_three]

theorem w_ne_zero (i : Fin 3) : w i ≠ 0 := by
  fin_cases i <;> simp [w]

theorem indefinite : (∃ v, 0 < Q v) ∧ ∃ v, Q v < 0 :=
  ⟨⟨Pi.single 0 1, by rw [Q_single]; simp [w]⟩,
    ⟨Pi.single 2 1, by rw [Q_single]; simp [w]⟩⟩

theorem nondegenerate : ∀ x, (∀ v, Q (v + x) = Q (v - x)) → x = 0 := by
  intro x hx
  funext i
  have h := hx (Pi.single i 1)
  rw [Q_apply, Q_apply] at h
  have key : 4 * (w i * x i) = 0 := by
    fin_cases i <;>
      simp [Fin.sum_univ_three, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff, -mul_eq_zero]
        at h ⊢ <;>
      linear_combination h
  have := w_ne_zero i
  simp only [Pi.zero_apply]
  rcases mul_eq_zero.mp key with h4 | h4
  · norm_num at h4
  · exact (mul_eq_zero.mp h4).resolve_left this

theorem double_sum_single (A : Matrix (Fin 3) (Fin 3) ℤ) (i : Fin 3) :
    (∑ k, ∑ j, (A k j : ℝ) * (Pi.single i (1 : ℝ) : Fin 3 → ℝ) k *
      (Pi.single i (1 : ℝ) : Fin 3 → ℝ) j) = A i i := by
  fin_cases i <;> simp [Fin.sum_univ_three]

theorem not_integral_multiple : ¬ ∃ (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℤ),
    ∀ x, Q x = c * ∑ i, ∑ j, (A i j : ℝ) * x i * x j := by
  rintro ⟨c, A, hA⟩
  have h0 := hA (Pi.single 0 1)
  have h2 := hA (Pi.single 2 1)
  rw [Q_single, double_sum_single] at h0 h2
  simp only [w] at h0 h2
  norm_num at h0 h2
  -- `1 = c * A₀₀` and `-√2 = c * A₂₂`, so `√2 = -A₂₂ / A₀₀` would be rational.
  have hA0 : (A 0 0 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at h0; norm_num at h0
  have hsqrt : Real.sqrt 2 = ((-A 2 2 / A 0 0 : ℚ) : ℝ) := by
    push_cast
    field_simp
    linear_combination (-(A 0 0 : ℝ)) * h2 + (A 2 2 : ℝ) * h0
  exact irrational_sqrt_two ⟨_, hsqrt.symm⟩

end MathlibExtTest.Dynamics.UnipotentFlowsHypotheses
