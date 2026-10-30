/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed

/-!
# Intertwining passes to the matrix exponential

If a rectangular matrix `X` intertwines two square matrices, `A * X = X * B`, then it
intertwines their exponentials: `exp A * X = X * exp B`. For `X` square and invertible this is
Mathlib's `Matrix.exp_conj`. The rectangular case is how a relation between two rate matrices
of continuous-time Markov chains, `Q * R = R * Q'`, passes to their transition matrices:
`exp (t Q) * R = R * exp (t Q')`. The proof pushes the intertwining through the exponential
series termwise (`A ^ k * X = X * B ^ k`).

## Main results

* `Matrix.exp_mul_eq_mul_exp_of_mul_eq`: `A * X = X * B → exp A * X = X * exp B`.

## References

Standard; the argument is the termwise comparison of the exponential series and needs no further
source.
-/

@[expose] public section

namespace Matrix

variable {𝕂 m n : Type*} [RCLike 𝕂] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Intertwining passes to the exponential.** If `A * X = X * B` for a rectangular matrix
`X`, then `exp A * X = X * exp B`. -/
theorem exp_mul_eq_mul_exp_of_mul_eq {A : Matrix m m 𝕂} {B : Matrix n n 𝕂} {X : Matrix m n 𝕂}
    (h : A * X = X * B) : NormedSpace.exp A * X = X * NormedSpace.exp B := by
  have hpow : ∀ k : ℕ, A ^ k * X = X * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  let L : Matrix m m 𝕂 →+ Matrix m n 𝕂 := AddMonoidHom.mk' (· * X) fun a b => Matrix.add_mul a b X
  let R : Matrix n n 𝕂 →+ Matrix m n 𝕂 := AddMonoidHom.mk' (X * ·) fun a b => Matrix.mul_add X a b
  have hL : Continuous L := continuous_id.matrix_mul continuous_const
  have hR : Continuous R := continuous_const.matrix_mul continuous_id
  open scoped Matrix.Norms.Operator in
  have hA := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) A).map L hL
  open scoped Matrix.Norms.Operator in
  have hB := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) B).map R hR
  refine hA.unique ?_
  convert hB using 1
  · funext k
    simp only [Function.comp_apply, L, R, AddMonoidHom.mk'_apply, Matrix.smul_mul,
      Matrix.mul_smul, hpow]
  · rfl

end Matrix
