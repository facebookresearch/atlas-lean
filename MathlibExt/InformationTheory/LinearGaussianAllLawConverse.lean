/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianJointLaw
public import MathlibExt.InformationTheory.ReferenceOutputKL
public import MathlibExt.InformationTheory.VectorGaussianKernelKL

/-!
# Log-determinant converse for the linear Gaussian channel under every input law

Let `H` be a real matrix from a finite input space to a nonempty finite output space and let `R`
be a positive definite noise covariance. Let `X` be an arbitrary input, not necessarily Gaussian
and not necessarily centered, under the finite-power model `E ‖X‖² ≤ P` with `0 ≤ P`
(`MathlibExt.InformationTheory.LinearGaussianJointLaw.PowerConstraint`), and let `K` be its
covariance. If `Z ~ N(0, R)` is independent of `X` and `Y = H X + Z`, then `K` is positive
semidefinite, `trace K ≤ P`, and

`I(X; Y) ≤ ofReal (log (det (R + H K Hᵀ) / det R) / (2 log 2))` bits

(`measureMutualInformation_linearGaussianChannel_le`; the law-level form, over every input law
with finite second moment, is `measureMutualInformation_compProd_noiseKernel_le`, and the
capacity form bounds the mutual information by the supremum over admissible covariances,
`measureMutualInformation_linearGaussianChannel_le_iSup`). The trace bound comes from the total
second moment `trace K + ‖m‖² ≤ P`, not from a centered input; the mean `m` does not appear in
the conclusion.

The proof compares the joint law with the input law times the moment-matched Gaussian reference
`N(H m, H K Hᵀ + R)`. The expected output quadratic form is a trace
(`integral_outputQuadratic_eq_trace`), so the closed-form kernel divergence
`MathlibExt.InformationTheory.VectorGaussianKernelKL.klDiv_compProd_noiseKernel` collapses to half
the log-determinant ratio (`gaussianKernelKLReal_outputMoments`,
`klDiv_compProd_noiseKernel_outputMoments`). The reference-output decomposition
`klDiv_prod_reference_eq_measureMutualInformation_add` from
`MathlibExt.InformationTheory.ReferenceOutputKL` then bounds the mutual information after
dropping the nonnegative output divergence.

Validation: a point mass at an arbitrary, possibly nonzero, mean gets the bound at `K = 0`
(`measureMutualInformation_dirac_compProd_noiseKernel_le`); the non-Gaussian two-point law
`(δ (c + a) + δ (c - a)) / 2` gets the bound at `a aᵀ`
(`measureMutualInformation_twoPoint_compProd_noiseKernel_le`). Without positive definite noise
the bound fails: the noiseless channel has infinite mutual information while the expression
evaluates to `0` (`not_measureMutualInformation_noiseless_le`).

Fading, channel-estimation error, multiuser channels, the equality case for Gaussian inputs and
optimization over `K` are not treated.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal

namespace MathlibExt.InformationTheory.LinearGaussianAllLawConverse

open _root_.InformationTheory

/-- Expected centered output quadratic form under an arbitrary finite-second-moment input law
`ρ` with mean `m` and covariance `K`: `E[(H x - H m)ᵀ A (H x - H m)] = trace (A H K Hᵀ)`, for
every real matrix `A`. -/
theorem integral_outputQuadratic_eq_trace {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (A : Matrix ι ι ℝ)
    (ρ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure ρ] (hρ : MemLp id 2 ρ)
    {m : EuclideanSpace ℝ κ} (hm : ∫ x, x ∂ρ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; ρ] = K a b) :
    ∫ x, ofLp (toEuclideanLin H x - toEuclideanLin H m) ⬝ᵥ
        A *ᵥ ofLp (toEuclideanLin H x - toEuclideanLin H m) ∂ρ =
      (A * (H * K * Hᵀ)).trace := by
  have hcoord : ∀ k, MemLp (fun x : EuclideanSpace ℝ κ => x k) 2 ρ :=
    fun k => hρ.eval_piLp k
  have hcoordInt : ∀ k, Integrable (fun x : EuclideanSpace ℝ κ => x k) ρ :=
    fun k => (hcoord k).integrable (by simp)
  have hmk : ∀ k, ∫ x, x k ∂ρ = m k := by
    intro k
    have h : (∫ x, x ∂ρ) k = ∫ x, x k ∂ρ :=
      eval_integral_piLp (f := fun x : EuclideanSpace ℝ κ => x) hcoordInt k
    rw [hm] at h
    exact h.symm
  have hE : ∀ k l, ∫ x, (x k - m k) * (x l - m l) ∂ρ = K k l := by
    intro k l
    have hfk : MemLp (fun x : EuclideanSpace ℝ κ => x k - m k) 2 ρ :=
      (hcoord k).sub (memLp_const (m k))
    have hfl : MemLp (fun x : EuclideanSpace ℝ κ => x l - m l) 2 ρ :=
      (hcoord l).sub (memLp_const (m l))
    have hmean0 : ∀ k, ∫ x, (x k - m k) ∂ρ = 0 := by
      intro k
      have hsub : ∫ x, (x k - m k) ∂ρ = ∫ x, x k ∂ρ - ∫ x, m k ∂ρ :=
        integral_sub (hcoordInt k) (integrable_const (m k))
      have hconst : ∫ x, m k ∂ρ = m k := by
        rw [integral_const, probReal_univ, one_smul]
      rw [hsub, hmk k, hconst, sub_self]
    have hcov : cov[fun x : EuclideanSpace ℝ κ => x k - m k,
        fun x => x l - m l; ρ]
        = ∫ x, ((x k - m k) * (x l - m l)) ∂ρ
          - (∫ x, (x k - m k) ∂ρ) * (∫ x, (x l - m l) ∂ρ) :=
      ProbabilityTheory.covariance_eq_sub hfk hfl
    rw [hmean0 k, hmean0 l, mul_zero, sub_zero] at hcov
    have hcov2 : cov[fun x : EuclideanSpace ℝ κ => x k - m k,
        fun x => x l - m l; ρ] = K k l := by
      have hsubL : cov[fun x : EuclideanSpace ℝ κ => x k - m k,
          fun x => x l - m l; ρ]
          = cov[fun x : EuclideanSpace ℝ κ => x k, fun x => x l - m l; ρ] :=
        ProbabilityTheory.covariance_sub_const_left (hcoordInt k) (m k)
      have hsubR : cov[fun x : EuclideanSpace ℝ κ => x k, fun x => x l - m l; ρ]
          = cov[fun x : EuclideanSpace ℝ κ => x k, fun x => x l; ρ] :=
        ProbabilityTheory.covariance_sub_const_right (hcoordInt l) (m l)
      rw [hsubL, hsubR]
      exact hK k l
    rw [← hcov]
    exact hcov2
  have hHx : ∀ (x : EuclideanSpace ℝ κ) (i : ι),
      (toEuclideanLin H x) i = ∑ k, H i k * x k := by
    intro x i
    change (Matrix.toLpLin 2 2 H x) i = ∑ k, H i k * x k
    rw [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec_apply_eq_sum]
  have hHm : ∀ i : ι, (toEuclideanLin H m) i = ∑ k, H i k * m k :=
    fun i => hHx m i
  have hvi : ∀ (x : EuclideanSpace ℝ κ) (i : ι),
      ofLp (toEuclideanLin H x - toEuclideanLin H m) i
        = ∑ k, H i k * (x k - m k) := by
    intro x i
    show (toEuclideanLin H x - toEuclideanLin H m) i = ∑ k, H i k * (x k - m k)
    rw [PiLp.sub_apply, hHx x i, hHm i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_sub]
  have hQ : ∀ x : EuclideanSpace ℝ κ,
      ofLp (toEuclideanLin H x - toEuclideanLin H m) ⬝ᵥ
          A *ᵥ ofLp (toEuclideanLin H x - toEuclideanLin H m)
        = ∑ i, ∑ j, A i j * ((∑ k, H i k * (x k - m k))
          * (∑ l, H j l * (x l - m l))) := by
    intro x
    have hexpand : ofLp (toEuclideanLin H x - toEuclideanLin H m) ⬝ᵥ
          A *ᵥ ofLp (toEuclideanLin H x - toEuclideanLin H m)
        = ∑ i, ∑ j, ofLp (toEuclideanLin H x - toEuclideanLin H m) i
          * (A i j * ofLp (toEuclideanLin H x - toEuclideanLin H m) j) := by
      change (∑ i, ofLp (toEuclideanLin H x - toEuclideanLin H m) i
        * (A *ᵥ ofLp (toEuclideanLin H x - toEuclideanLin H m)) i)
        = ∑ i, ∑ j, ofLp (toEuclideanLin H x - toEuclideanLin H m) i
          * (A i j * ofLp (toEuclideanLin H x - toEuclideanLin H m) j)
      simp only [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    rw [hexpand]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hvi x i, hvi x j]
    ring
  have hS : ∀ i, MemLp (fun x : EuclideanSpace ℝ κ => ∑ k, H i k * (x k - m k)) 2 ρ :=
    fun i => memLp_finsetSum _ (fun k _ =>
      ((hcoord k).sub (memLp_const (m k))).const_mul (H i k))
  have hT : ∀ j, MemLp (fun x : EuclideanSpace ℝ κ => ∑ l, H j l * (x l - m l)) 2 ρ :=
    fun j => memLp_finsetSum _ (fun l _ =>
      ((hcoord l).sub (memLp_const (m l))).const_mul (H j l))
  have hIntInner : ∀ i j, Integrable (fun x : EuclideanSpace ℝ κ =>
      A i j * ((∑ k, H i k * (x k - m k)) * (∑ l, H j l * (x l - m l)))) ρ :=
    fun i j => ((hS i).integrable_mul (hT j)).const_mul (A i j)
  have hIntOuter : ∀ i, Integrable (fun x : EuclideanSpace ℝ κ =>
      ∑ j, A i j * ((∑ k, H i k * (x k - m k)) * (∑ l, H j l * (x l - m l)))) ρ :=
    fun i => integrable_finsetSum _ (fun j _ => hIntInner i j)
  have hval : ∀ i j, ∫ x, A i j * ((∑ k, H i k * (x k - m k))
      * (∑ l, H j l * (x l - m l))) ∂ρ
      = A i j * (∑ k, ∑ l, H i k * H j l * K k l) := by
    intro i j
    rw [integral_const_mul]
    congr 1
    have hexp : ∀ x : EuclideanSpace ℝ κ,
        (∑ k, H i k * (x k - m k)) * (∑ l, H j l * (x l - m l))
        = ∑ k, ∑ l, (H i k * (x k - m k)) * (H j l * (x l - m l)) := by
      intro x
      rw [Finset.sum_mul_sum]
    simp only [hexp]
    have hIntL : ∀ k l, Integrable (fun x : EuclideanSpace ℝ κ =>
        (H i k * (x k - m k)) * (H j l * (x l - m l))) ρ := by
      intro k l
      exact (((hcoord k).sub (memLp_const (m k))).const_mul (H i k)).integrable_mul
        (((hcoord l).sub (memLp_const (m l))).const_mul (H j l))
    have hIntK : ∀ k, Integrable (fun x : EuclideanSpace ℝ κ =>
        ∑ l, (H i k * (x k - m k)) * (H j l * (x l - m l))) ρ :=
      fun k => integrable_finsetSum _ (fun l _ => hIntL k l)
    rw [integral_finsetSum _ (fun k _ => hIntK k)]
    have hswapK : (∑ k, ∫ x, (∑ l, (H i k * (x k - m k))
        * (H j l * (x l - m l))) ∂ρ)
        = ∑ k, ∑ l, ∫ x, (H i k * (x k - m k)) * (H j l * (x l - m l)) ∂ρ :=
      Finset.sum_congr rfl (fun k _ => integral_finsetSum _ (fun l _ => hIntL k l))
    rw [hswapK]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    have hring : ∀ x : EuclideanSpace ℝ κ,
        (H i k * (x k - m k)) * (H j l * (x l - m l))
        = (H i k * H j l) * ((x k - m k) * (x l - m l)) :=
      fun x => by ring
    simp only [hring]
    rw [integral_const_mul, hE k l]
  simp only [hQ]
  rw [integral_finsetSum _ (fun i _ => hIntOuter i)]
  have hswapJ : (∑ i, ∫ x, (∑ j, A i j * ((∑ k, H i k * (x k - m k))
      * (∑ l, H j l * (x l - m l)))) ∂ρ)
      = ∑ i, ∑ j, ∫ x, A i j * ((∑ k, H i k * (x k - m k))
        * (∑ l, H j l * (x l - m l))) ∂ρ :=
    Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hIntInner i j))
  rw [hswapJ]
  simp only [hval]
  have hsym : ∀ k l, K k l = K l k := by
    intro k l
    rw [← hK k l, ← hK l k, ProbabilityTheory.covariance_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsym k l]
  ring

/-- The kernel closed form at the moment-matched Gaussian reference `N(H m, H K Hᵀ + R)`
collapses to the log-det value: the trace term `trace (T⁻¹ (R + H K Hᵀ)) = d` cancels the
dimension. -/
theorem gaussianKernelKLReal_outputMoments {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (ρ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure ρ] (hρ : MemLp id 2 ρ)
    {m : EuclideanSpace ℝ κ} (hm : ∫ x, x ∂ρ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; ρ] = K a b) :
    VectorGaussianKernelKL.gaussianKernelKLReal H (toEuclideanLin H m) R (H * K * Hᵀ + R) ρ =
      Real.log ((R + H * K * Hᵀ).det / R.det) / 2 := by
  have hKpsd : K.PosSemidef :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.posSemidef_of_covariance
      (X := id) hρ hK
  have hT : (H * K * Hᵀ + R).PosDef :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.posDef_output_covariance H hKpsd hR
  have hTdet : IsUnit (H * K * Hᵀ + R).det :=
    isUnit_iff_ne_zero.mpr hT.det_pos.ne'
  have hInt := integral_outputQuadratic_eq_trace H ((H * K * Hᵀ + R)⁻¹) ρ hρ hm hK
  have hsum : ((H * K * Hᵀ + R)⁻¹ * R).trace + ((H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ)).trace
      = (Fintype.card ι : ℝ) := by
    have hmul : (H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ + R)
        = (H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ) + (H * K * Hᵀ + R)⁻¹ * R :=
      mul_add _ _ _
    have h1 : ((H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ + R)).trace = (Fintype.card ι : ℝ) := by
      rw [Matrix.nonsing_inv_mul _ hTdet, Matrix.trace_one]
    rw [hmul, Matrix.trace_add] at h1
    linear_combination h1
  simp only [MathlibExt.InformationTheory.VectorGaussianKernelKL.gaussianKernelKLReal]
  rw [hInt]
  have hadd : H * K * Hᵀ + R = R + H * K * Hᵀ := add_comm _ _
  have hdet : (H * K * Hᵀ + R).det = (R + H * K * Hᵀ).det := by rw [hadd]
  rw [hdet]
  have h2 : Real.log ((R + H * K * Hᵀ).det / R.det) - (Fintype.card ι : ℝ)
      + ((H * K * Hᵀ + R)⁻¹ * R).trace + ((H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ)).trace
      = Real.log ((R + H * K * Hᵀ).det / R.det) := by
    linear_combination hsum
  rw [h2]

/-- The kernel divergence against the moment-matched Gaussian reference, in nats. -/
theorem klDiv_compProd_noiseKernel_outputMoments {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (ρ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure ρ]
    (hρ : MemLp id 2 ρ) {m : EuclideanSpace ℝ κ} (hm : ∫ x, x ∂ρ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; ρ] = K a b) :
    klDiv (ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R))
      (ρ.prod (multivariateGaussian (toEuclideanLin H m) (H * K * Hᵀ + R))) =
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / 2) := by
  have hKpsd : K.PosSemidef :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.posSemidef_of_covariance
      (X := id) hρ hK
  have hT : (H * K * Hᵀ + R).PosDef :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.posDef_output_covariance H hKpsd hR
  rw [MathlibExt.InformationTheory.VectorGaussianKernelKL.klDiv_compProd_noiseKernel _ _ _ _
    hR hT _ hρ, gaussianKernelKLReal_outputMoments H hR ρ hρ hm hK]

/-- **Law-level all-law converse.** For every finite-second-moment input law `ρ` (any mean,
not necessarily Gaussian) with covariance `K`, and the noise kernel of `N(0, R)` with `R`
positive definite, the mutual information of the joint law, in bits, is at most the Gaussian
log-det value at `K`. -/
theorem measureMutualInformation_compProd_noiseKernel_le {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (ρ : Measure (EuclideanSpace ℝ κ))
    [IsProbabilityMeasure ρ] (hρ : MemLp id 2 ρ) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; ρ] = K a b) :
    measureMutualInformation
        (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  have hm : ∫ x, x ∂ρ = ∫ x, x ∂ρ := rfl
  have hkl : klDiv (ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R))
      (ρ.prod (multivariateGaussian (toEuclideanLin H (∫ x, x ∂ρ)) (H * K * Hᵀ + R))) =
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / 2) :=
    klDiv_compProd_noiseKernel_outputMoments (m := ∫ x, x ∂ρ) H hR ρ hρ hm hK
  have hdecomp : klDiv (ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R))
      (((ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)).map Prod.fst).prod
        (multivariateGaussian (toEuclideanLin H (∫ x, x ∂ρ)) (H * K * Hᵀ + R))) =
      ENNReal.ofReal (Real.log 2) * measureMutualInformation
          (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
            (MetaMathlibExt.continuous_toEuclideanLin H).measurable
            (multivariateGaussian 0 R), inferInstance⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι))
        + klDiv ((ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable
          (multivariateGaussian 0 R)).map Prod.snd)
          (multivariateGaussian (toEuclideanLin H (∫ x, x ∂ρ)) (H * K * Hᵀ + R)) :=
    ReferenceOutputKL.klDiv_prod_reference_eq_measureMutualInformation_add
      (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
        inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) _
  have hfst : (ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
      (MetaMathlibExt.continuous_toEuclideanLin H).measurable
      (multivariateGaussian 0 R)).map Prod.fst = ρ :=
    MeasureTheory.Measure.fst_compProd _ _
  rw [hfst, hkl] at hdecomp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb0 : ENNReal.ofReal (Real.log 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hlog2).ne'
  have hbtop : ENNReal.ofReal (Real.log 2) ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  have hMI : measureMutualInformation
        (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / 2)
        / ENNReal.ofReal (Real.log 2) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)]
    rw [mul_comm]
    rw [hdecomp]
    exact le_add_of_nonneg_right bot_le
  have hdiv : ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / 2)
      / ENNReal.ofReal (Real.log 2)
      = ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
    rw [← ENNReal.ofReal_div_of_pos hlog2, div_div]
  rw [hdiv] at hMI
  exact hMI

/-- **All-law log-det converse for the linear Gaussian channel** (headline). For an arbitrary
input `X` under the finite-power model `E ‖X‖² ≤ P`, `P ≥ 0`, with covariance `K`, noise
`Z ~ N(0, R)` with `R` positive definite and independent of `X`, and `Y = H X + Z`: `K` is
positive semidefinite, `trace K ≤ P`, and
`I(X; Y) ≤ ofReal (log (det (R + H K Hᵀ) / det R) / (2 log 2))` bits. -/
theorem measureMutualInformation_linearGaussianChannel_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hZ : Measurable Z) (hind : IndepFun X Z μ)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) {P : ℝ}
    (hpow : LinearGaussianJointLaw.PowerConstraint μ X P) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) :
    K.PosSemidef ∧ K.trace ≤ P ∧
      measureMutualInformation
          (⟨μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)), inferInstance⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
        ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  have hX2 : MemLp X 2 μ :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.PowerConstraint.memLp_two
      hpow hX.aestronglyMeasurable
  have hpsd : K.PosSemidef :=
    MathlibExt.InformationTheory.LinearGaussianJointLaw.posSemidef_of_covariance hX2 hK
  have htrace : K.trace ≤ P := by
    have hsum :=
      LinearGaussianJointLaw.trace_add_norm_sq_le_of_powerConstraint hX hpow rfl hK
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hsum
  refine ⟨hpsd, htrace, ?_⟩
  have hρ : MemLp id 2 (μ.map X) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hX.aemeasurable).mpr hX2
  have hKmap : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; μ.map X]
      = K a b := by
    intro a b
    have hcoord_ae : ∀ c, AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ κ => x c) (μ.map X) :=
      fun c => (hρ.eval_piLp c).aestronglyMeasurable
    rw [ProbabilityTheory.covariance_map_fun (hcoord_ae a) (hcoord_ae b) hX.aemeasurable]
    exact hK a b
  have hJ : (⟨μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι))
      = ⟨μ.map X ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
        inferInstance⟩ :=
    Subtype.ext
      (LinearGaussianJointLaw.map_prod_eq_compProd_noiseKernel H hX hZ hind hZlaw)
  rw [hJ]
  exact measureMutualInformation_compProd_noiseKernel_le H hR (μ.map X) hρ hKmap

/-- Capacity-form corollary: under the same hypotheses, the mutual information is at most the
supremum of the log-det value over positive semidefinite covariances of trace at most `P`. -/
theorem measureMutualInformation_linearGaussianChannel_le_iSup {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {X : Ω → EuclideanSpace ℝ κ}
    {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R) {P : ℝ}
    (hpow : LinearGaussianJointLaw.PowerConstraint μ X P) :
    measureMutualInformation
        (⟨μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
      ⨆ (K' : Matrix κ κ ℝ) (_ : K'.PosSemidef ∧ K'.trace ≤ P),
        ENNReal.ofReal (Real.log ((R + H * K' * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  obtain ⟨hpsd, htrace, hmi⟩ :=
    measureMutualInformation_linearGaussianChannel_le
      (K := fun a b => cov[fun ω => X ω a, fun ω => X ω b; μ])
      H hR hX hZ hind hZlaw hpow (fun a b => rfl)
  exact le_iSup_of_le (fun a b => cov[fun ω => X ω a, fun ω => X ω b; μ])
    (le_iSup_of_le ⟨hpsd, htrace⟩ hmi)

/-! ### Validation statements -/

/-- Validation, nonzero-mean point mass: for an input fixed at an arbitrary `c` (covariance
`0`), the converse bound is the log-det value at `K = 0`, which is `0`. -/
theorem measureMutualInformation_dirac_compProd_noiseKernel_le {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (c : EuclideanSpace ℝ κ) :
    measureMutualInformation
        (⟨Measure.dirac c ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal
        (Real.log ((R + H * (0 : Matrix κ κ ℝ) * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  have hMem : MemLp id 2 (Measure.dirac c) := memLp_dirac enorm_lt_top
  have hK0 : ∀ a b, cov[fun x : EuclideanSpace ℝ κ => x a, fun x => x b; Measure.dirac c]
      = (0 : Matrix κ κ ℝ) a b := by
    intro a b
    simp only [ProbabilityTheory.covariance, integral_dirac]
    rw [sub_self, zero_mul, Matrix.zero_apply]
  exact measureMutualInformation_compProd_noiseKernel_le H hR (Measure.dirac c) hMem
    (K := 0) hK0

/-- Validation, non-Gaussian nonzero-mean finite mixture: the two-point law
`(δ (c + a) + δ (c - a)) / 2` has mean `c` and covariance `a aᵀ`, and the converse bound is the
log-det value at `a aᵀ`. -/
theorem measureMutualInformation_twoPoint_compProd_noiseKernel_le {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (c a : EuclideanSpace ℝ κ)
    (ρ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure ρ]
    (hρ : ρ = (1 / 2 : ℝ≥0∞) • Measure.dirac (c + a) + (1 / 2 : ℝ≥0∞) • Measure.dirac (c - a)) :
    measureMutualInformation
        (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal (Real.log ((R + H * vecMulVec (ofLp a) (ofLp a) * Hᵀ).det / R.det) /
        (2 * Real.log 2)) := by
  have h12r : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have h12 : (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    intro h
    rw [h, ENNReal.toReal_top] at h12r
    norm_num at h12r
  have hIntSmul : ∀ (f : EuclideanSpace ℝ κ → ℝ) (p : EuclideanSpace ℝ κ),
      Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac p) :=
    fun f p => (((memLp_dirac enorm_lt_top : MemLp f 2 (Measure.dirac p)).integrable
      (by simp)).smul_measure h12)
  have hMem : MemLp id 2 ρ := by
    rw [hρ]
    exact ((memLp_dirac enorm_lt_top).smul_measure h12).add_measure
      ((memLp_dirac enorm_lt_top).smul_measure h12)
  have hcoordMem : ∀ i, MemLp (fun x : EuclideanSpace ℝ κ => x i) 2 ρ :=
    fun i => hMem.eval_piLp i
  have hmean : ∀ i, ∫ x, x i ∂ρ = c i := by
    intro i
    rw [hρ, integral_add_measure (hIntSmul _ _) (hIntSmul _ _)]
    simp only [integral_smul_measure, integral_dirac, PiLp.add_apply, PiLp.sub_apply,
      smul_eq_mul, h12r]
    ring
  have hprod : ∀ i j, ∫ x, x i * x j ∂ρ = c i * c j + a i * a j := by
    intro i j
    rw [hρ, integral_add_measure (hIntSmul _ _) (hIntSmul _ _)]
    simp only [integral_smul_measure, integral_dirac, PiLp.add_apply, PiLp.sub_apply,
      smul_eq_mul, h12r]
    ring
  have hK8 : ∀ i j, cov[fun x : EuclideanSpace ℝ κ => x i, fun x => x j; ρ]
      = Matrix.vecMulVec (ofLp a) (ofLp a) i j := by
    intro i j
    have hcov : cov[fun x : EuclideanSpace ℝ κ => x i, fun x => x j; ρ]
        = ∫ x, (x i * x j) ∂ρ - (∫ x, x i ∂ρ) * (∫ x, x j ∂ρ) :=
      ProbabilityTheory.covariance_eq_sub (hcoordMem i) (hcoordMem j)
    rw [hprod i j, hmean i, hmean j] at hcov
    rw [Matrix.vecMulVec_apply, hcov]
    ring
  exact measureMutualInformation_compProd_noiseKernel_le H hR ρ hMem hK8

open scoped MatrixOrder in
/-- The degenerate Gaussian with zero covariance on `Fin 1` is the point mass at its mean. -/
private theorem multivariateGaussian_zero_zero_fin_one :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (0 : Matrix (Fin 1) (Fin 1) ℝ) =
      Measure.dirac 0 := by
  rw [multivariateGaussian, CFC.sqrt_zero]
  simp

/-- Violated premise, `R = 0` (not positive definite): for the noiseless channel `Y = X` with
`X ~ N(0, 1)` on `Fin 1` the mutual information is `⊤`, so it is not bounded by the log-det
expression, which evaluates to `0`. -/
theorem not_measureMutualInformation_noiseless_le :
    ¬ measureMutualInformation
        (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) ≤
      ENNReal.ofReal (Real.log (((0 : Matrix (Fin 1) (Fin 1) ℝ) +
          1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det /
          (0 : Matrix (Fin 1) (Fin 1) ℝ).det) / (2 * Real.log 2)) := by
  have hmat : (0 : Matrix (Fin 1) (Fin 1) ℝ)
      + 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
      = 1 := by
    rw [Matrix.transpose_one, mul_one, mul_one, zero_add]
  have hdet1 : ((0 : Matrix (Fin 1) (Fin 1) ℝ)
      + 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det
      = 1 := by
    rw [hmat, Matrix.det_one]
  have hdet0 : (0 : Matrix (Fin 1) (Fin 1) ℝ).det = 0 := by
    rw [Matrix.det_fin_one, Matrix.zero_apply]
  have hexpr : Real.log (((0 : Matrix (Fin 1) (Fin 1) ℝ) +
      1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det /
      (0 : Matrix (Fin 1) (Fin 1) ℝ).det) / (2 * Real.log 2) = 0 := by
    rw [hdet1, hdet0, div_zero, Real.log_zero, zero_div]
  have hN00 : multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
      (0 : Matrix (Fin 1) (Fin 1) ℝ) = Measure.dirac 0 :=
    multivariateGaussian_zero_zero_fin_one
  have hf1 : ∀ y : EuclideanSpace ℝ (Fin 1),
      toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) y = y := by
    intro y
    change Matrix.toLpLin 2 2 (1 : Matrix (Fin 1) (Fin 1) ℝ) y = y
    rw [Matrix.toLpLin_one, LinearMap.id_apply]
  have hκ : ∀ y, MetaMathlibExt.noiseKernel
      (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (MetaMathlibExt.continuous_toEuclideanLin _).measurable
      (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)) y
      = Measure.dirac y := by
    intro y
    rw [MetaMathlibExt.noiseKernel_apply, hN00, Measure.map_dirac' (measurable_const_add _)]
    congr 1
    show toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) y + 0 = y
    rw [add_zero, hf1 y]
  have hfst9 : (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
      MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))).map Prod.fst
      = multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    MeasureTheory.Measure.fst_compProd _ _
  have hsnd : (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
      MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))).map Prod.snd
      = multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext1 s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.compProd_apply (measurable_snd hs)]
    have hset : ∀ a : EuclideanSpace ℝ (Fin 1), Prod.mk a ⁻¹' (Prod.snd ⁻¹' s) = s :=
      fun a => Set.ext fun y => Iff.rfl
    simp only [hset, hκ, Measure.dirac_apply, lintegral_indicator_one hs]
  have hDmeas : MeasurableSet (Set.diagonal (EuclideanSpace ℝ (Fin 1))) :=
    measurableSet_diagonal
  have hmkdiag : ∀ x : EuclideanSpace ℝ (Fin 1),
      Prod.mk x ⁻¹' Set.diagonal (EuclideanSpace ℝ (Fin 1)) = ({x} : Set _) := by
    intro x
    ext y
    simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_singleton_iff]
    exact eq_comm
  have hJ1 : (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
      MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)))
      (Set.diagonal (EuclideanSpace ℝ (Fin 1))) = 1 := by
    rw [Measure.compProd_apply hDmeas]
    have h1 : ∀ x, MetaMathlibExt.noiseKernel
        (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)) x
        (Prod.mk x ⁻¹' Set.diagonal (EuclideanSpace ℝ (Fin 1))) = 1 := by
      intro x
      rw [hκ x, hmkdiag x]
      exact Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr rfl)
    simp only [h1, lintegral_one]
    simp
  have hPSD1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.posSemidef_diagonal_iff]
    exact fun _ => zero_le_one
  have hBilin1 : ∀ x y : EuclideanSpace ℝ (Fin 1),
      ProbabilityTheory.covarianceBilin
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) x y
        = x ⬝ᵥ (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ y :=
    fun x y => ProbabilityTheory.covarianceBilin_multivariateGaussian hPSD1 x y
  have hBilinDirac : ∀ (z) (x y : EuclideanSpace ℝ (Fin 1)),
      ProbabilityTheory.covarianceBilin (Measure.dirac z) x y = 0 := by
    intro z x y
    have hMem : MemLp id 2 (Measure.dirac z) := memLp_dirac enorm_lt_top
    rw [ProbabilityTheory.covarianceBilin_apply_eq_cov hMem]
    simp only [ProbabilityTheory.covariance, integral_dirac]
    rw [sub_self, zero_mul]
  have hsingle : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ⬝ᵥ
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (EuclideanSpace.single 0 1) = 1 := by
    change ofLp (EuclideanSpace.single (0 : Fin 1) (1:ℝ)) ⬝ᵥ
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ofLp (EuclideanSpace.single 0 1) = 1
    rw [PiLp.ofLp_single, Matrix.one_mulVec]
    simp [dotProduct]
  have hNe : ∀ y, multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠ Measure.dirac y := by
    intro y hcon
    have h1 := hBilin1 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    have h0 := hBilinDirac y (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    rw [hcon] at h1
    rw [h0, hsingle] at h1
    exact one_ne_zero h1.symm
  have hNull : MeasureTheory.NullSingletonClass
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ProbabilityTheory.IsGaussian.nullSingletonClass hNe
  have hP0 : (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).prod
      (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Set.diagonal (EuclideanSpace ℝ (Fin 1))) = 0 := by
    rw [Measure.prod_apply hDmeas]
    have h0 : ∀ x, (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (Prod.mk x ⁻¹' Set.diagonal (EuclideanSpace ℝ (Fin 1))) = 0 := by
      intro x
      rw [hmkdiag x]
      exact hNull.measure_singleton x
    simp only [h0, lintegral_zero]
  have hNotAc : ¬ (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
      MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))) ≪
      (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).prod
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    intro h
    have hcon := h hP0
    rw [hJ1] at hcon
    exact one_ne_zero hcon
  have hklTop : klDiv (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
      MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin _).measurable
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)))
      ((multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).prod
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))) = ∞ :=
    InformationTheory.klDiv_of_not_ac hNotAc
  have hMI : measureMutualInformation
      (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable
          (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
        inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) = ⊤ := by
    have hunfold : measureMutualInformation
        (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
        = klDiv (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)))
          (((multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
            MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
              (MetaMathlibExt.continuous_toEuclideanLin _).measurable
              (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))).map Prod.fst).prod
            ((multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
              MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
                (MetaMathlibExt.continuous_toEuclideanLin _).measurable
                (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))).map Prod.snd))
          / ENNReal.ofReal (Real.log 2) := rfl
    rw [hunfold, hfst9, hsnd, hklTop,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_lt_top.ne]
  rw [hexpr, hMI, ENNReal.ofReal_zero]
  exact fun h => ENNReal.zero_ne_top (top_le_iff.mp h)

end MathlibExt.InformationTheory.LinearGaussianAllLawConverse
