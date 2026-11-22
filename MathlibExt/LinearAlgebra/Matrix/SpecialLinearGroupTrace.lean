/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

namespace MetaMathlibExt

open Matrix Matrix.SpecialLinearGroup

/-- **Trace identities in $\mathrm{SL}(2, \mathbb{Z})$.** For all $A, B \in \mathrm{SL}(2,
\mathbb{Z})$ we have $\operatorname{tr} A = \operatorname{tr} A^{-1}$,
$\operatorname{tr}(AB) = \operatorname{tr} A \cdot \operatorname{tr} B -
\operatorname{tr}(AB^{-1})$, and $A^2 = (\operatorname{tr} A) A - I$, where $I$ is the
identity matrix.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.6 (citing Aigner, Lemma 4.2). -/
public theorem specialLinearGroup_two_trace_identities
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ∧
      Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℤ) -
          Matrix.trace ((A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
            Matrix (Fin 2) (Fin 2) ℤ) ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) • (A : Matrix (Fin 2) (Fin 2) ℤ) - 1 := by
  have mul_add_mul_inv (X Y : SpecialLinearGroup (Fin 2) ℤ) :
      (X * Y).1 + (X * Y⁻¹).1 = Y.1.trace • X.1 := by
    have h : Y.1 + (Y⁻¹).1 = Y.1.trace • 1 := by
      rw [coe_inv, adjugate_fin_two, trace_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [add_comm]
    rw [coe_mul, coe_mul, ← mul_add, h, Matrix.mul_smul, mul_one]
  refine ⟨?_, eq_sub_of_add_eq ?_, eq_sub_of_add_eq ?_⟩
  · rw [coe_inv, adjugate_fin_two, trace_fin_two_of, trace_fin_two, add_comm]
  · simpa only [trace_add, trace_smul, smul_eq_mul, mul_comm] using
      congrArg Matrix.trace (mul_add_mul_inv A B)
  · simpa only [mul_inv_cancel, coe_one, coe_mul, pow_two] using mul_add_mul_inv A A

end MetaMathlibExt
