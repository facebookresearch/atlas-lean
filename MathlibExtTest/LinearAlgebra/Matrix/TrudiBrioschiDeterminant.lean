/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant

namespace MetaMathlibExt

example (a : ℕ → ℤ) : toeplitzHessenbergDet a 1 = a 1 := toeplitzHessenbergDet_one a

example (a : ℕ → ℤ) : toeplitzHessenbergDet a 2 = a 1 ^ 2 - a 0 * a 2 :=
  toeplitzHessenbergDet_two a

example : toeplitzHessenbergDet (fun _ => (1 : ℤ)) 0 = 1 := by
  simp [toeplitzHessenbergDet]

/-- With `a_0 = 1` and `a_i = 1` the composition form gives `∑_c (-1)^{3 - ℓ(c)}` over the
compositions of `3`. -/
example : toeplitzHessenbergDet (fun _ => (1 : ℤ)) 3 =
    ∑ c : Composition 3, (-1 : ℤ) ^ (3 - c.length) * ∏ _r : Fin c.length, (1 : ℤ) :=
  toeplitzHessenbergDet_eq_sum_compositions _ 3

example : trudiPartitionSum (1 : ℤ) (fun _ => 1) 4 = 8 := trudiPartitionSum_examples.1

example : trudiPartitionSum (2 : ℤ) (fun _ => 1) 2 = 6 := by decide

/-- Over the semiring `ℕ`, the all-ones partition sum counts the compositions of `n`. -/
example (n : ℕ) : trudiPartitionSum (1 : ℕ) (fun _ => 1) n = Fintype.card (Composition n) := by
  simp [trudiPartitionSum_eq_sum_compositions]

/-- `∑_{α̃ = 3} m_3(α) 1^{α₁} 2^{α₂} 3^{α₃} = 1 + 4 + 3`, matching the compositions
`3, 1 + 2, 2 + 1, 1 + 1 + 1` with weights `3, 2, 2, 1`. -/
example : trudiPartitionSum (1 : ℤ) (fun i => i) 3 = 8 := by decide

example : toeplitzHessenbergDet (fun i => if i = 0 then (1 : ℤ) else i) 3 =
    (-1) ^ 3 * trudiPartitionSum (-1) (fun i => if i = 0 then (1 : ℤ) else i) 3 :=
  toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum _ (by simp) 3

example : toeplitzHessenbergDet (fun i => if i = 0 then (-1 : ℤ) else i) 3 =
    trudiPartitionSum 1 (fun i => if i = 0 then (-1 : ℤ) else i) 3 :=
  toeplitzHessenbergDet_eq_trudiPartitionSum_one _ (by simp) 3

/-- `D_-(1, 2, 3) = 8` through the `a_0 = -1` specialization. -/
example : toeplitzHessenbergDet (fun i => if i = 0 then (-1 : ℤ) else i) 3 = 8 := by
  rw [toeplitzHessenbergDet_eq_trudiPartitionSum_one _ (by simp)]
  decide

end MetaMathlibExt
