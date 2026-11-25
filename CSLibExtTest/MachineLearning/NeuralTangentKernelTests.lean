/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import CSLibExt.MachineLearning.NeuralTangentKernel
public import MathlibExt.Analysis.Calculus.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Tests for the empirical neural tangent kernel
-/

@[expose] public section

open scoped Matrix

namespace CSLibExtTest.MachineLearning.NeuralTangentKernel

open Cslib.MachineLearning.NeuralTangentKernel

/-- Linear model: the NTK is constant and equals the linear kernel. -/
theorem test_linear_const (X : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : X = !![1, 2; 0, 1])
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : F = fun θ : EuclideanSpace ℝ (Fin 2) => WithLp.toLp 2 (X *ᵥ ⇑θ)) :
    ntk 2 2 F (WithLp.toLp 2 ![0, 0])
        = ntk 2 2 F (WithLp.toLp 2 ![1, -1])
      ∧ ntk 2 2 F (WithLp.toLp 2 ![0, 0]) = !![5, 2; 2, 1] := by
  have h1 := ntk_linear 2 2 X F hF (WithLp.toLp 2 ![0, 0])
  have h2 := ntk_linear 2 2 X F hF (WithLp.toLp 2 ![1, -1])
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
  · rw [h1, hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Zero residual: the kernel-applied residual vanishes; reading this as
zero output velocity needs the gradient-flow hypothesis. -/
theorem test_zero_residual_zero_velocity (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : ℝ → EuclideanSpace ℝ (Fin P))
    (t : ℝ) (h : F (θ t) = y) :
    WithLp.toLp 2 ((ntk P n F (θ t)) *ᵥ ⇑(F (θ t) - y)) = 0 := by
  have h0 : ⇑(0 : EuclideanSpace ℝ (Fin n)) = (0 : Fin n → ℝ) := rfl
  have h1 : WithLp.toLp 2 (0 : Fin n → ℝ) = (0 : EuclideanSpace ℝ (Fin n)) := rfl
  rw [h, sub_self, h0, Matrix.mulVec_zero, h1]

/-- Scalar identity model: the NTK is the `1 × 1` identity. -/
theorem test_scalar_ntk (θ : EuclideanSpace ℝ (Fin 1)) :
    ntk 1 1 (fun θ' => θ') θ = 1 := by
  have hF : (fun θ' => θ')
      = fun θ'' : EuclideanSpace ℝ (Fin 1) =>
        WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ⇑θ'') := by
    funext θ''
    simp [Matrix.one_mulVec]
  have h := ntk_linear 1 1 1 (fun θ' => θ') hF θ
  rw [h, Matrix.transpose_one, Matrix.mul_one]

/-- Scalar identity model: evaluates the NTK-applied residual expression
(no derivative occurs in the statement). -/
theorem test_scalar_flow (y : EuclideanSpace ℝ (Fin 1))
    (θ : ℝ → EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    (-(WithLp.toLp 2 ((ntk 1 1 (fun θ' => θ') (θ t)) *ᵥ ⇑(θ t - y)))) 0
      = -((θ t) 0 - y 0) := by
  rw [test_scalar_ntk, Matrix.one_mulVec]
  simp [PiLp.sub_apply]

private theorem jac_scalar_identity (θ : EuclideanSpace ℝ (Fin 1)) :
    jac 1 1 (fun θ' => θ') θ = 1 := by
  have hfun : (fun x : Fin 1 → ℝ =>
      ⇑((fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (WithLp.toLp 2 x)))
      = fun y => (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ y := by
    funext x
    show ⇑(WithLp.toLp 2 x) = (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x
    rw [Matrix.one_mulVec]
  show MetaMathlibExt.jacobianMatrix
    (fun x : Fin 1 → ℝ =>
      ⇑((fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (WithLp.toLp 2 x))) ⇑θ = 1
  rw [hfun]
  exact MetaMathlibExt.jacobianMatrix_fun_mulVec (1 : Matrix (Fin 1) (Fin 1) ℝ) ⇑θ

/-- The transported `jac` agrees with the canonical Jacobian on the scalar identity. -/
theorem test_jac_agrees_canonical (θ : EuclideanSpace ℝ (Fin 1)) :
    jac 1 1 (fun θ' => θ') θ
      = MetaMathlibExt.jacobianMatrix (fun x : Fin 1 → ℝ => x) ⇑θ := by
  have hfun : (fun x : Fin 1 → ℝ =>
      ⇑((fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (WithLp.toLp 2 x)))
      = fun x : Fin 1 → ℝ => x := by
    funext x
    exact WithLp.ofLp_toLp 2 x
  show MetaMathlibExt.jacobianMatrix
    (fun x : Fin 1 → ℝ =>
      ⇑((fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (WithLp.toLp 2 x))) ⇑θ
    = MetaMathlibExt.jacobianMatrix (fun x : Fin 1 → ℝ => x) ⇑θ
  rw [hfun]

/-- Scalar identity model: the square-loss gradient at distinct parameter and target. -/
theorem test_scalar_gradient :
    gradient (sqLoss 1 1 (fun θ' => θ') (WithLp.toLp 2 ![1])) (WithLp.toLp 2 ![3])
      = WithLp.toLp 2 ![2] := by
  have hCont : ContDiff ℝ 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') := contDiff_id
  have hJac := jac_scalar_identity (WithLp.toLp 2 ![3])
  have hGrad := gradient_sqLoss 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ')
    (WithLp.toLp 2 ![1]) (WithLp.toLp 2 ![3]) hCont
  rw [hJac, Matrix.transpose_one, Matrix.one_mulVec] at hGrad
  rw [hGrad]
  congr 1
  ext i
  fin_cases i
  simp
  norm_num

/-- Scalar identity model: gradient flow at one time with nonzero residual. -/
theorem test_scalar_flow_deriv :
    HasDerivAt (fun s : ℝ => (fun θ' : EuclideanSpace ℝ (Fin 1) => θ')
      ((WithLp.toLp 2 ![3] : EuclideanSpace ℝ (Fin 1)) +
        s • (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1))))
      (WithLp.toLp 2 ![-2]) (0 : ℝ) := by
  set traj : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun s => (WithLp.toLp 2 ![3] : EuclideanSpace ℝ (Fin 1)) +
      s • (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1)) with htraj
  set y : EuclideanSpace ℝ (Fin 1) := (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)) with hy
  have hCont : ContDiff ℝ 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') := contDiff_id
  have htraj0 : traj 0 = (WithLp.toLp 2 ![3] : EuclideanSpace ℝ (Fin 1)) := by
    simp [htraj]
  have hJac := jac_scalar_identity (traj 0)
  have hGrad := gradient_sqLoss 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') y (traj 0) hCont
  rw [hJac, Matrix.transpose_one, Matrix.one_mulVec] at hGrad
  have hGradVal : gradient (sqLoss 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') y) (traj 0)
      = (WithLp.toLp 2 ![2] : EuclideanSpace ℝ (Fin 1)) := by
    rw [hGrad]
    rw [htraj0]
    congr 1
    ext i
    fin_cases i
    simp [hy]
    norm_num
  have hDeriv : HasDerivAt traj (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1)) 0 := by
    have hid : HasDerivAt (fun s : ℝ => s • (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1)))
        ((1 : ℝ) • (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1))) (0 : ℝ) :=
      HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) _
    rw [one_smul] at hid
    have h := hid.const_add (WithLp.toLp 2 ![3] : EuclideanSpace ℝ (Fin 1))
    simp only [htraj] at h ⊢
    exact h
  have hNeg : (-gradient (sqLoss 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') y) (traj 0))
      = (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1)) := by
    rw [hGradVal]
    ext i
    fin_cases i
    simp
  have hθ : HasDerivAt traj
      (-gradient (sqLoss 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') y) (traj 0))
      0 := by
    rw [hNeg]
    exact hDeriv
  have hFlow := gradient_flow_identity 1 1
    (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') y traj hCont 0 hθ
  have hNtk : ntk 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (traj 0) = 1 :=
    test_scalar_ntk (traj 0)
  have hVal : (-(WithLp.toLp 2
    ((ntk 1 1 (fun θ' : EuclideanSpace ℝ (Fin 1) => θ') (traj 0)) *ᵥ ⇑(traj 0 - y))))
      = (WithLp.toLp 2 ![-2] : EuclideanSpace ℝ (Fin 1)) := by
    rw [hNtk, Matrix.one_mulVec, htraj0]
    ext i
    fin_cases i
    simp [hy]
    norm_num
  rw [hVal] at hFlow
  simp only [htraj] at hFlow ⊢
  exact hFlow

noncomputable def quadModel : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
  fun θ => ((θ 0) ^ 2) •
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))

private theorem quadModel_contDiff : ContDiff ℝ 2 quadModel := by
  unfold quadModel
  have hproj : ContDiff ℝ 2 (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0) := by
    have h : (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0) =
      ⇑(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) := rfl
    rw [h]
    exact (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).contDiff
  have hpow : ContDiff ℝ 2 (fun θ : EuclideanSpace ℝ (Fin 1) => (θ 0) ^ 2) :=
    ContDiff.pow hproj 2
  have hconst : ContDiff ℝ 2
      (fun _ : EuclideanSpace ℝ (Fin 1) =>
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))) :=
    contDiff_const
  exact ContDiff.smul hpow hconst

private theorem quadModel_hasFDerivAt (θ : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt quadModel
      ((2 * (θ 0)) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))) θ := by
  unfold quadModel
  have hproj : HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0)
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) θ := by
    have h : (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0) =
      ⇑(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) := rfl
    rw [h]
    exact ContinuousLinearMap.hasFDerivAt _
  have hpow := HasFDerivAt.pow hproj 2
  have hsm := HasFDerivAt.smul_const hpow
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))
  simp only [Nat.reduceSub, pow_one] at hsm
  convert hsm using 2
  ext x
  simp [ContinuousLinearMap.smulRight_apply, mul_comm]

private theorem quadModel_fderiv_eq (θ : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ quadModel θ = (2 * (θ 0)) •
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) :=
  (quadModel_hasFDerivAt θ).fderiv

private theorem quadModel_second_hasFDerivAt (θ' : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt
      (fun θ : EuclideanSpace ℝ (Fin 1) =>
        (2 * (θ 0)) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)))
      (((2 : ℝ) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0)).smulRight
        ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))))
        θ' := by
  have hproj : HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0)
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) θ' := by
    have h : (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0) =
      ⇑(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) := rfl
    rw [h]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 : HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin 1) => (2 : ℝ) * (θ 0))
      ((2 : ℝ) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0)) θ' :=
    hproj.const_smul (2 : ℝ)
  exact HasFDerivAt.smul_const h2
    ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)))

private theorem quad_single_norm : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :
    EuclideanSpace ℝ (Fin 1))‖ = 1 := by
  have h : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) =
    PiLp.single 2 (0 : Fin 1) (1 : ℝ) := rfl
  rw [h, PiLp.norm_single]
  simp

private theorem quad_fin1_norm (u : EuclideanSpace ℝ (Fin 1)) : ‖u‖ = ‖u 0‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

private theorem quadModel_fderiv_fun_eq :
    fderiv ℝ quadModel = fun θ : EuclideanSpace ℝ (Fin 1) =>
      (2 * (θ 0)) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) := by
  funext θ
  exact quadModel_fderiv_eq θ

private theorem quadModel_hessian (θ' : EuclideanSpace ℝ (Fin 1))
    (u v : EuclideanSpace ℝ (Fin 1)) :
    ‖(fderiv ℝ (fderiv ℝ quadModel) θ' u) v‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  have hSecond : HasFDerivAt (fderiv ℝ quadModel)
      (((2 : ℝ) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0)).smulRight
        ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))))
        θ' := by
    rw [quadModel_fderiv_fun_eq]
    exact quadModel_second_hasFDerivAt θ'
  have hF2 := hSecond.fderiv
  rw [hF2]
  have hDu :
      ((((2 : ℝ) • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0)).smulRight
        ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).smulRight
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))))
      u) v
      = ((2 * (u 0) * (v 0)) •
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1))) := by
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
    rw [← mul_smul]
  rw [hDu]
  rw [norm_smul, Real.norm_eq_abs]
  rw [quad_single_norm, mul_one]
  rw [quad_fin1_norm u, quad_fin1_norm v]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have h : |2 * (u 0) * (v 0)| = 2 * |u 0| * |v 0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [h]

/-- Quadratic model: one gradient step with explicit remainder bound. -/
theorem test_quad_onestep :
    ‖quadModel ((WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)) -
      (1/2 : ℝ) • gradient (sqLoss 1 1 quadModel
        (WithLp.toLp 2 ![0] : EuclideanSpace ℝ (Fin 1)))
        (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)))
        - quadModel (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1))
        + (1/2 : ℝ) • WithLp.toLp 2
          ((ntk 1 1 quadModel (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1))) *ᵥ
            ⇑(quadModel (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)) -
              (WithLp.toLp 2 ![0] : EuclideanSpace ℝ (Fin 1))))‖
      ≤ ((2 : ℝ)/2) * (1/2 : ℝ)^2 *
        ‖gradient (sqLoss 1 1 quadModel (WithLp.toLp 2 ![0] : EuclideanSpace ℝ (Fin 1)))
          (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1))‖^2 := by
  have hF := quadModel_contDiff
  have hβ : (0:ℝ) ≤ 2 := by norm_num
  have hH : ∀ θ' ∈ segment ℝ (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1))
      ((WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)) -
        (1/2 : ℝ) • gradient (sqLoss 1 1 quadModel
          (WithLp.toLp 2 ![0] : EuclideanSpace ℝ (Fin 1)))
          (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1))),
      ∀ u v, ‖(fderiv ℝ (fderiv ℝ quadModel) θ' u) v‖ ≤ 2 * ‖u‖ * ‖v‖ := by
    intro θ' _ u v
    exact quadModel_hessian θ' u v
  exact one_step_gd_remainder 1 1 quadModel (WithLp.toLp 2 ![0] : EuclideanSpace ℝ (Fin 1))
    (WithLp.toLp 2 ![1] : EuclideanSpace ℝ (Fin 1)) (1/2) 2 hF hβ hH

#print axioms gradient_sqLoss
#print axioms gradient_flow_identity
#print axioms one_step_gd_remainder
#print axioms ntk_linear

end CSLibExtTest.MachineLearning.NeuralTangentKernel
