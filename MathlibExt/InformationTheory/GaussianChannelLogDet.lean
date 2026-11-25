/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianJointLaw
public import MathlibExt.LinearAlgebra.Matrix.FischerDeterminant
public import MathlibExt.InformationTheory.ReferenceOutputKL
public import MathlibExt.InformationTheory.VectorGaussianKernelKL

/-!
# Log-determinant mutual information of a Gaussian-input linear Gaussian channel

Let `H` be a real matrix from a finite input space to a nonempty finite output space, let `K` be
a positive semidefinite input covariance (singular covariances included), and let `R` be a
positive definite noise covariance. If `X ~ N(0, K)` and `Z ~ N(0, R)` are independent and
`Y = H X + Z`, then the mutual information of `(X, Y)`, in bits, is

`I(X; Y) = ofReal (log (det (R + H K Hᵀ) / det R) / (2 log 2))`

(`measureMutualInformation_linearGaussianChannel_gaussianInput`; the law-level form is
`measureMutualInformation_gaussianInput_compProd_noiseKernel`). Both determinants are strictly
positive (`det_pos_noise_and_output`) and the gain is nonnegative (`log_det_ratio_nonneg`).

Scope: this module evaluates the mutual information at one fixed input covariance `K`; it
defines no capacity and proves no capacity theorem. The all-law converse
`measureMutualInformation_linearGaussianChannel_le_iSup`, in
`MathlibExt.InformationTheory.LinearGaussianAllLawConverse`, bounds the mutual information of
every input with `E ‖X‖² ≤ P` by the supremum of the same log-det value over positive
semidefinite `K` with `trace K ≤ P`; the value computed here is what a centered Gaussian input
with covariance `K` attains. The power constraint for Gaussian inputs, the identification of the
capacity with that supremum, and its water-filling evaluation are not proved here.

The proof compares the joint law with the input law times the actual output law
`N(0, H K Hᵀ + R)` (`map_snd_gaussianInput_compProd_noiseKernel`, which needs only a positive
semidefinite, possibly singular, noise covariance). The closed-form kernel divergence
`MathlibExt.InformationTheory.VectorGaussianKernelKL.klDiv_compProd_noiseKernel` then
collapses to half the log-determinant ratio
(`klDiv_gaussianInput_compProd_noiseKernel_outputLaw`), so no input density and no limit over a
support subspace is needed.

Validation: a zero input covariance gives `0` (`measureMutualInformation_gaussianInput_zero`), a
rank-one covariance `v vᵀ` gives `log (1 + (H v)ᵀ R⁻¹ (H v)) / (2 log 2)` by the matrix
determinant lemma (`measureMutualInformation_gaussianInput_rankOne`), the full-rank nondiagonal
covariance `[[2, 1], [1, 2]]` with `H = R = 1` gives `3 / 2` bits
(`measureMutualInformation_gaussianInput_nondiagonal`), and the `1 × 1` case is the scalar
Gaussian channel formula (`measureMutualInformation_gaussianInput_fin_one`). Without positive
definite noise the formula fails: the noiseless channel has infinite mutual information while the
expression evaluates to `0` (`measureMutualInformation_noiseless_ne_logDet`).

Fading, channel-estimation error, multiuser channels, power constraints and optimization over
`K` are not treated.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  §9.5 (channels with colored Gaussian noise), eqs. (9.81)-(9.82), with Theorem 8.4.1 (entropy of
  a multivariate normal distribution, `h(N(μ, K)) = (1/2) log ((2πe)ⁿ |K|)` bits). For
  `Y = X + Z` with `X ~ N(0, K_X)` independent of `Z ~ N(0, K_Z)`, these give
  `I(X; Y) = h(Y) - h(Z) = (1/2) log (|K_X + K_Z| / |K_Z|)` bits, the case `H = 1`, `K = K_X`,
  `R = K_Z` of the formula above, with the same factor `1/2`.

The source states the formula for the identity channel matrix and does not discuss singular input
covariances. The extension to a general `H` and to singular positive semidefinite `K` is derived
here, not taken from the source: the proof never uses a density of `X`, only that the output
covariance `R + H K Hᵀ` is positive definite, which holds because `R` is.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal

namespace MathlibExt.InformationTheory.GaussianChannelLogDet

open _root_.InformationTheory

open scoped MatrixOrder

private theorem map_fst_compProd' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).map Prod.fst = μ :=
  Measure.fst_compProd μ κ

/-- Both determinants of the log-det ratio are strictly positive: `det R > 0` and
`det (R + H K Hᵀ) > 0`, for `K` positive semidefinite and `R` positive definite. -/
theorem det_pos_noise_and_output {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : Matrix ι κ ℝ) {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) :
    0 < R.det ∧ 0 < (R + H * K * Hᵀ).det := by
  rw [add_comm R]
  exact ⟨hR.det_pos, (LinearGaussianJointLaw.posDef_output_covariance H hK hR).det_pos⟩

/-- The log-det gain is nonnegative: `det R ≤ det (R + H K Hᵀ)`. -/
theorem log_det_ratio_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : Matrix ι κ ℝ) {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) :
    0 ≤ Real.log ((R + H * K * Hᵀ).det / R.det) := by
  have hD : (R + H * K * Hᵀ - R).PosSemidef := by
    rw [add_sub_cancel_left, ← conjTranspose_eq_transpose_of_trivial]
    exact hK.mul_mul_conjTranspose_same H
  exact Real.log_nonneg ((one_le_div hR.det_pos).2 (det_le_det_of_posSemidef_le hR.posSemidef hD))

/-- The output law of the Gaussian-input channel: the second marginal of
`N(0, K) ⊗ₘ noiseKernel` is `N(0, H K Hᵀ + R)`, for `K` and `R` positive semidefinite (both
possibly singular). -/
theorem map_snd_gaussianInput_compProd_noiseKernel {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {K : Matrix κ κ ℝ} (hK : K.PosSemidef)
    {R : Matrix ι ι ℝ} (hR : R.PosSemidef) :
    (multivariateGaussian 0 K ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)).map Prod.snd =
      multivariateGaussian 0 (H * K * Hᵀ + R) := by
  have hg : Measurable (fun q : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      (q.1, toEuclideanLin H q.1 + q.2)) :=
    measurable_fst.prodMk
      (((MetaMathlibExt.continuous_toEuclideanLin H).measurable.comp measurable_fst).add
        measurable_snd)
  rw [VectorGaussianKernelKL.compProd_noiseKernel_eq_map, Measure.map_map measurable_snd hg]
  have hc : (Prod.snd ∘ fun q : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      (q.1, toEuclideanLin H q.1 + q.2)) = fun q => toEuclideanLin H q.1 + q.2 := rfl
  have hind : IndepFun Prod.fst Prod.snd
      ((multivariateGaussian (0 : EuclideanSpace ℝ κ) K).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) R)) :=
    (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).2 (by simp)
  rw [hc, MetaMathlibExt.map_linear_add_of_indepFun (m := 0) (c := 0) measurable_fst
    measurable_snd hind hK hR (by simp) (by simp) H]
  simp

/-- The kernel divergence against the actual output law: with `Q = N(0, H K Hᵀ + R)`, the
closed form collapses to `log (det (R + H K Hᵀ) / det R) / 2`, in nats. -/
theorem klDiv_gaussianInput_compProd_noiseKernel_outputLaw {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    klDiv (multivariateGaussian 0 K ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R))
      ((multivariateGaussian 0 K).prod (multivariateGaussian 0 (H * K * Hᵀ + R))) =
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / 2) := by
  have hT : (H * K * Hᵀ + R).PosDef :=
    LinearGaussianJointLaw.posDef_output_covariance H hK hR
  rw [VectorGaussianKernelKL.klDiv_compProd_noiseKernel H 0 R _ hR hT _ IsGaussian.memLp_two_id,
    VectorGaussianKernelKL.gaussianKernelKLReal_gaussianInput H 0 R _ 0 K hK]
  have htr : ((H * K * Hᵀ + R)⁻¹ * R).trace + ((H * K * Hᵀ + R)⁻¹ * (H * K * Hᵀ)).trace =
      (Fintype.card ι : ℝ) := by
    rw [← trace_add, ← Matrix.mul_add, add_comm R, nonsing_inv_mul _ hT.det_pos.ne'.isUnit,
      trace_one]
  rw [add_comm (H * K * Hᵀ) R] at htr ⊢
  congr 1
  simp only [map_zero, sub_zero, ofLp_zero, zero_dotProduct, add_zero]
  linarith

/-- **Law-level log-det formula.** For centered Gaussian input law `N(0, K)` with `K`
positive semidefinite (possibly singular) and the noise kernel of `N(0, R)` with `R` positive
definite, the mutual information of the joint law, in bits, is
`ofReal (log (det (R + H K Hᵀ) / det R) / (2 log 2))`. -/
theorem measureMutualInformation_gaussianInput_compProd_noiseKernel {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    measureMutualInformation
        (⟨multivariateGaussian 0 K ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  unfold measureMutualInformation
  simp only [ProbabilityMeasure.coe_mk]
  rw [map_fst_compProd', map_snd_gaussianInput_compProd_noiseKernel H hK hR.posSemidef,
    klDiv_gaussianInput_compProd_noiseKernel_outputLaw H hK hR,
    ← ENNReal.ofReal_div_of_pos (Real.log_pos one_lt_two), div_div]

/-- **Mutual information of the Gaussian-input linear Gaussian channel** (headline). For
`X ~ N(0, K)` with `K` positive semidefinite (possibly singular), `Z ~ N(0, R)` with `R`
positive definite, `Z` independent of `X`, and `Y = H X + Z`,
`I(X; Y) = ofReal (log (det (R + H K Hᵀ) / det R) / (2 log 2))` bits. -/
theorem measureMutualInformation_linearGaussianChannel_gaussianInput {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (hXlaw : μ.map X = multivariateGaussian 0 K)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) :
    measureMutualInformation
        (⟨μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (Real.log ((R + H * K * Hᵀ).det / R.det) / (2 * Real.log 2)) := by
  have key : (⟨μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) =
      ⟨multivariateGaussian 0 K ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
        inferInstance⟩ := by
    apply Subtype.ext
    change μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)) = _
    rw [LinearGaussianJointLaw.map_prod_eq_compProd_noiseKernel H hX hZ hind hZlaw, hXlaw]
  rw [key]
  exact measureMutualInformation_gaussianInput_compProd_noiseKernel H hK hR

/-! ### Validation statements -/

private theorem multivariateGaussian_zero_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) (0 : Matrix ι ι ℝ) = Measure.dirac 0 := by
  simp [multivariateGaussian, CFC.sqrt_zero]

/-- Validation, `K = 0`: a zero-covariance (point-mass) Gaussian input carries no information. -/
theorem measureMutualInformation_gaussianInput_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) :
    measureMutualInformation
        (⟨multivariateGaussian 0 (0 : Matrix κ κ ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin H)
            (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) = 0 := by
  have _ := hR
  have hJ : multivariateGaussian 0 (0 : Matrix κ κ ℝ) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) =
      (Measure.dirac 0).prod (MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable
          (multivariateGaussian 0 R) 0) := by
    rw [multivariateGaussian_zero_zero]
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.prod_apply hs, lintegral_dirac]
  have key : (⟨multivariateGaussian 0 (0 : Matrix κ κ ℝ) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
        inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) =
      ⟨(Measure.dirac 0).prod (MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) 0),
        inferInstance⟩ := Subtype.ext hJ
  rw [key, ReferenceOutputKL.measureMutualInformation_prod_eq_zero]

/-- Validation, rank-one `K = v vᵀ` (singular as soon as `card κ ≥ 2`): by the matrix
determinant lemma the value is `log (1 + (H v)ᵀ R⁻¹ (H v)) / (2 log 2)` bits. -/
theorem measureMutualInformation_gaussianInput_rankOne {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    (v : κ → ℝ) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    measureMutualInformation
        (⟨multivariateGaussian 0 (vecMulVec v v) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin H)
            (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ κ × EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (Real.log (1 + (H *ᵥ v) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ v)) / (2 * Real.log 2)) := by
  have hK : (vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  rw [measureMutualInformation_gaussianInput_compProd_noiseKernel H hK hR]
  have hM : H * vecMulVec v v * Hᵀ =
      replicateCol Unit (H *ᵥ v) * replicateRow Unit (H *ᵥ v) := by
    rw [vecMulVec_eq Unit, replicateCol_mulVec, replicateRow_mulVec, transpose_mul,
      transpose_replicateCol]
    simp only [Matrix.mul_assoc]
  have hd : (R + H * vecMulVec v v * Hᵀ).det / R.det = 1 + (H *ᵥ v) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ v) := by
    rw [hM, det_add_replicateCol_mul_replicateRow hR.det_pos.ne'.isUnit,
      mul_div_cancel_left₀ _ hR.det_pos.ne', Matrix.mul_assoc, ← replicateCol_mulVec,
      replicateRow_mul_replicateCol, det_unique]
    simp
  rw [hd]

private theorem posSemidef_two_one :
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  have hB : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1, 1, 0; 1, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ) *
        (!![1, 1, 0; 1, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ)ᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  rw [hB]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Validation, full-rank nondiagonal example: `H = 1`, `R = 1`, `K = [[2, 1], [1, 2]]` on
`Fin 2`. Then `det (1 + K) = 8`, so the mutual information is `3 / 2` bits. -/
theorem measureMutualInformation_gaussianInput_nondiagonal :
    measureMutualInformation
        (⟨multivariateGaussian 0 (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      ENNReal.ofReal (3 / 2) := by
  rw [measureMutualInformation_gaussianInput_compProd_noiseKernel _ posSemidef_two_one
    PosDef.one]
  have hdet : ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
      1 * (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ).det
        = 8 := by
    rw [Matrix.det_fin_two]
    simp
    norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hdet, Matrix.det_one, div_one, h8]
  congr 1
  field_simp

/-- Validation, scalar instance `n = m = 1`: gain `h`, input variance `k ≥ 0`, noise variance
`r > 0`. The value is the scalar Gaussian channel formula `log (1 + h² k / r) / (2 log 2)`. -/
theorem measureMutualInformation_gaussianInput_fin_one (h k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    measureMutualInformation
        (⟨multivariateGaussian 0 (!![k] : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (!![h] : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (!![r] : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
      ENNReal.ofReal (Real.log (1 + h ^ 2 * k / r) / (2 * Real.log 2)) := by
  have hKd : (!![k] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => k := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hRd : (!![r] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => r := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hK : (!![k] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
    rw [hKd]
    exact posSemidef_diagonal_iff.2 fun _ => hk
  have hR : (!![r] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    rw [hRd]
    exact posDef_diagonal_iff.2 fun _ => hr
  rw [measureMutualInformation_gaussianInput_compProd_noiseKernel _ hK hR]
  have hd : ((!![r] : Matrix (Fin 1) (Fin 1) ℝ) +
        (!![h] : Matrix (Fin 1) (Fin 1) ℝ) * (!![k] : Matrix (Fin 1) (Fin 1) ℝ) *
          (!![h] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det /
        (!![r] : Matrix (Fin 1) (Fin 1) ℝ).det = 1 + h ^ 2 * k / r := by
    rw [Matrix.det_fin_one, Matrix.det_fin_one]
    simp [Matrix.vecMul, dotProduct, Matrix.vecHead, Function.swap]
    field_simp
  rw [hd]

/-- Violated premise, `R = 0` (not positive definite): the noiseless channel `Y = X` with
`X ~ N(0, 1)` on `Fin 1` has infinite mutual information, while the log-det expression
evaluates to `0` (Lean's `x / 0 = 0`), so the formula fails without `R.PosDef`. -/
theorem measureMutualInformation_noiseless_ne_logDet :
    measureMutualInformation
        (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
        ⊤ ∧
      ENNReal.ofReal (Real.log (((0 : Matrix (Fin 1) (Fin 1) ℝ) +
          1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det /
          (0 : Matrix (Fin 1) (Fin 1) ℝ).det) / (2 * Real.log 2)) = 0 := by
  refine ⟨?_, by simp⟩
  have hf := (MetaMathlibExt.continuous_toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).measurable
  have hid : ∀ x : EuclideanSpace ℝ (Fin 1), toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) x = x :=
    fun x => by
      apply WithLp.ofLp_injective
      exact Matrix.one_mulVec (ofLp x)
  have hκ : ∀ x, MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)) hf
      (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)) x = Measure.dirac x := by
    intro x
    rw [MetaMathlibExt.noiseKernel_apply, multivariateGaussian_zero_zero,
      Measure.map_dirac' (measurable_const_add _), hid, add_zero]
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (1 : Matrix (Fin 1) (Fin 1) ℝ)
  set J := N ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)) hf
      (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ))
  have hD : MeasurableSet {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hJD : J {p | p.1 = p.2} = 1 := by
    rw [Measure.compProd_apply hD]
    have : ∀ x, MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)) hf
        (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)) x
          (Prod.mk x ⁻¹' {p | p.1 = p.2}) = 1 := by
      intro x
      rw [hκ]
      exact Measure.dirac_apply_of_mem (by simp)
    simp_rw [this]
    simp
  have hsing : ∀ x : EuclideanSpace ℝ (Fin 1), N {x} = 0 := by
    intro x
    have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1)))
      (PosSemidef.one (n := Fin 1) (R := ℝ)) (i := 0)
    have : (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1 := rfl
    have := nullSingletonClass_gaussianReal (μ := ((0 : EuclideanSpace ℝ (Fin 1)) 0))
      (v := ((1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0).toNNReal) (by simp)
    refine nonpos_iff_eq_zero.1 ?_
    calc N {x} ≤ N ((fun y : EuclideanSpace ℝ (Fin 1) => y 0) ⁻¹' {x 0}) :=
          measure_mono fun y hy => by simp_all
      _ = 0 := by rw [← Measure.map_apply hmp.measurable (measurableSet_singleton _), hmp.map_eq,
          measure_singleton]
  have hPD : (N.prod N) {p | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hD]
    have : ∀ x : EuclideanSpace ℝ (Fin 1), N (Prod.mk x ⁻¹' {p | p.1 = p.2}) = 0 := by
      intro x
      have hs : Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) |
          p.1 = p.2} = {x} := by
        ext y
        simp [eq_comm]
      rw [hs, hsing]
    simp [hsing]
  have hfst : J.map Prod.fst = N := map_fst_compProd' _ _
  have hsnd : J.map Prod.snd = N := by
    rw [map_snd_gaussianInput_compProd_noiseKernel _ PosSemidef.one PosSemidef.zero]
    simp [N]
  have hnac : ¬ J ≪ (J.map Prod.fst).prod (J.map Prod.snd) := by
    intro hac
    rw [hfst, hsnd] at hac
    have := hac hPD
    rw [hJD] at this
    exact one_ne_zero this
  unfold measureMutualInformation
  simp only [ProbabilityMeasure.coe_mk]
  rw [klDiv_of_not_ac hnac]
  exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

end MathlibExt.InformationTheory.GaussianChannelLogDet
