/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.KacWardCactusAssembly
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open scoped BigOperators

namespace StatMech.FrontierA

open Matrix StatMech.Onsager



def kwThetaLeftDirection : Fin 3 -> Fin 4 := ![1, 0, 3]



def kwThetaRightDirection : Fin 3 -> Fin 4 := ![1, 2, 3]




noncomputable def kwThetaForwardInternal (omega : ℂ) : Fin 3 -> ℂ :=
  ![(omega⁻¹) ^ 2, 1, omega ^ 2]


noncomputable def kwThetaReverseInternal (omega : ℂ) : Fin 3 -> ℂ :=
  ![omega ^ 2, 1, (omega⁻¹) ^ 2]



noncomputable def kwThetaForward (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then 0 else
    x i * kwThetaForwardInternal omega i *
      ons_turnW omega (kwThetaRightDirection i + 2) (kwThetaRightDirection j)



noncomputable def kwThetaReverse (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then 0 else
    x i * kwThetaReverseInternal omega i *
      ons_turnW omega (kwThetaLeftDirection i + 2) (kwThetaLeftDirection j)


noncomputable def kwThetaTransition (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks 0 (kwThetaForward omega x) (kwThetaReverse omega x) 0



noncomputable def kwThetaEvenPolynomial (x : Fin 3 -> ℂ) : ℂ :=
  1 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2

theorem kwTheta_one_sub (omega : ℂ) (x : Fin 3 -> ℂ) :
    1 - kwThetaTransition omega x =
      Matrix.fromBlocks 1 (-kwThetaForward omega x)
        (-kwThetaReverse omega x) 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [kwThetaTransition, Matrix.one_apply]



theorem kacWard_theta (omega : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (x : Fin 3 -> ℂ) :
    (1 - kwThetaTransition omega x).det = (kwThetaEvenPolynomial x) ^ 2 := by
  rw [kwTheta_one_sub, Matrix.det_fromBlocks_one₁₁]
  have hnegMul :
      (-kwThetaReverse omega x) * (-kwThetaForward omega x) =
        kwThetaReverse omega x * kwThetaForward omega x := by
    simp
  rw [hnegMul, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_three]
  simp [kwThetaForward, kwThetaReverse, kwThetaForwardInternal,
    kwThetaReverseInternal, kwThetaLeftDirection, kwThetaRightDirection,
    ons_turnW]
  field_simp
  have h4 : omega ^ 4 = -1 := ons_omega_pow_four omega hI
  have h8 : omega ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add, h4]
    norm_num
  have h12 : omega ^ 12 = -1 := by
    rw [show (12 : ℕ) = 4 + 8 by norm_num, pow_add, h4, h8]
    norm_num
  rw [h4, h8, h12]
  unfold kwThetaEvenPolynomial
  ring

end StatMech.FrontierA
