/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Code.ChapterII.CovarianceMatrix
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# CDIS Probabilités IV: multidimensional central limit theorem

* id 80: if `X_1, X_2, ...` are i.i.d. square-integrable random vectors in `ℝ^d` with mean `m`
  and covariance matrix `C`, then `(S_n - n m) / √n` converges in law to the centered Gaussian
  vector with covariance matrix `C` (Mathlib's `multivariateGaussian 0 C`).

Proof: by Cramér-Wold it suffices to show `⟪(S_n - n m) / √n, t⟫ → ⟪Z, t⟫` for every `t`. The
left side is the one-dimensional normalised sum of the i.i.d. variables `⟪X_k, t⟫`, whose
variance is `tᵀ C t` (id 40), and `⟪Z, t⟫` has law `N(0, tᵀ C t)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace CDIS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma inner_eq_sum_mul (x t : EuclideanSpace ℝ ι) : ⟪x, t⟫ = ∑ i, t i * x i := by
  simp [PiLp.inner_apply, mul_comm]

/-- `⟪Z, t⟫` has law `N(0, tᵀ C t)` when `Z` has law `multivariateGaussian 0 C`. -/
lemma hasLaw_inner_multivariateGaussian {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {Z : Ω' → EuclideanSpace ℝ ι}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P') (t : EuclideanSpace ℝ ι) :
    HasLaw (fun ω ↦ ⟪Z ω, t⟫) (gaussianReal 0 (t ⬝ᵥ C *ᵥ t).toNNReal) P' := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) C
  set L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ t
  have hL : HasLaw L (gaussianReal 0 (t ⬝ᵥ C *ᵥ t).toNNReal) μ := by
    refine ⟨L.continuous.measurable.aemeasurable, ?_⟩
    rw [IsGaussian.map_eq_gaussianReal L,
      ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
    congr
    have hvar : Var[L; μ] = covarianceBilin μ t t := by
      rw [covarianceBilin_self IsGaussian.memLp_two_id]
      rfl
    rw [hvar, covarianceBilin_multivariateGaussian hC]
  have := hL.fun_comp hZ
  refine this.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [L, innerSL_apply_apply, real_inner_comm]

/-- CDIS P.IV, id 80 (multidimensional central limit theorem). -/
theorem tendstoInDistribution_multivariate_clt {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X : ℕ → Ω → EuclideanSpace ℝ ι} (h2 : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {Z : Ω' → EuclideanSpace ℝ ι}
    (hZ : HasLaw Z (multivariateGaussian 0 (covMatrix (fun i ω ↦ X 0 ω i) P)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ • (∑ k ∈ range n, X k ω - (n : ℝ) • ∫ ω, X 0 ω ∂P))
      atTop Z (fun _ ↦ P) P' := by
  set C := covMatrix (fun i ω ↦ X 0 ω i) P
  have hcoord : ∀ i, MemLp (fun ω ↦ X 0 ω i) 2 P := fun i ↦
    (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ ι)).comp_memLp' h2
  have hC : C.PosSemidef := covMatrix_posSemidef hcoord
  have hXmeas : ∀ n, AEMeasurable (X n) P := fun n ↦ (hident n).aemeasurable_fst
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner hZ.aemeasurable fun n ↦ by
    fun_prop]
  intro t
  set Y : ℕ → Ω → ℝ := fun k ω ↦ ⟪X k ω, t⟫
  have hinner : Measurable fun x : EuclideanSpace ℝ ι ↦ ⟪x, t⟫ := by fun_prop
  have hY2 : MemLp (Y 0) 2 P := by
    have := (innerSL ℝ t : StrongDual ℝ (EuclideanSpace ℝ ι)).comp_memLp' h2
    refine this.ae_eq (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp [Y, real_inner_comm]
  have hYindep : iIndepFun Y P := hindep.comp (fun _ x ↦ ⟪x, t⟫) fun _ ↦ hinner
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i ↦ (hident i).comp hinner
  have hVar : Var[Y 0; P] = t ⬝ᵥ C *ᵥ t := by
    rw [dotProduct_covMatrix_mulVec hcoord t]
    congr 1
  have hW := hasLaw_inner_multivariateGaussian hC hZ t
  rw [← hVar] at hW
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hW hY2 hYindep hYident
  have hmean : ∫ ω, Y 0 ω ∂P = ⟪∫ ω, X 0 ω ∂P, t⟫ := by
    rw [real_inner_comm, ← integral_inner (h2.integrable one_le_two) t]
    simp only [Y, real_inner_comm]
  convert hclt using 2 with n
  funext ω
  simp only [Y, hmean, inner_smul_left, inner_sub_left, sum_inner, RCLike.conj_to_real]

end CDIS
