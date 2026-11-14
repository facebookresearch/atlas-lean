/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.OLSConsistency
public import MathlibExt.Probability.Statistics.LinearModel.HeteroskedasticityRobust
public import MathlibExt.Probability.Statistics.MultivariateCLT
public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import MathlibExt.Probability.Distributions.GaussianConditioning

/-!
# Asymptotic normality of OLS with i.i.d. rows (Atlas ST05.T02)

Stacked on ST05.T01 (`OLSConsistency`): same random-design model, i.i.d.
rows `(xᵢ, uᵢ)`, observed responses `yᵢ = xᵢ ⬝ᵥ β + uᵢ`, moment exogeneity
`𝔼[x₀ u₀] = 0`, nonsingular population Gram `Q = 𝔼[x₀ x₀ᵀ]`, plus
square-integrability of the score `x₀ u₀`. Then
`√n (β̂ₙ - β) →ᵈ N(0, Q⁻¹ Ω Q⁻¹)` with `Ω = 𝔼[(x₀ u₀)(x₀ u₀)ᵀ]`
the sandwich (meat) matrix `popScoreCov`.

Proof route (the CLT and Slutsky are not reproved): the multivariate CLT
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_smul_sum_sub` gives
`√n • (n⁻¹ ∑ xᵢ uᵢ) →ᵈ N(0, Ω)`; ST05.T01 (`tendsto_sampleGram_ae`) gives
`Q̂ₙ → Q` a.s., hence `Q̂ₙ⁻¹ → Q⁻¹` in probability, entrywise in `k → k → ℝ`;
Slutsky (`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`
with `g (v, A) = A *ᵥ v`) sends `Q̂ₙ⁻¹ *ᵥ (√n • n⁻¹ ∑ xᵢ uᵢ)` to the image of `N(0, Ω)`
under `Q⁻¹`, which is `N(0, Q⁻¹ Ω Q⁻¹)` by
`MetaMathlibExt.map_toEuclideanLin_multivariateGaussian` (`Q` is symmetric). By
`olsSeqEstimator_eq` the discrepancy `√n (β̂ₙ - β) - Q̂ₙ⁻¹ *ᵥ (√n • n⁻¹ ∑ xᵢ uᵢ)` is `0`
whenever `Q̂ₙ` is a unit, and `P(Q̂ₙ not a unit) → 0`, so it tends to `0` in probability;
`tendstoInDistribution_of_tendstoInMeasure_sub` closes the argument.

`popScoreCov_eq_hc0PopMeat` and `popScoreCov_sandwich_eq_hc0PopSandwich` identify the meat and
the limit covariance with `hc0PopMeat` and `hc0PopSandwich` of `HeteroskedasticityRobust`, whose
robust Wald theorem `tendsto_coverage_hc0Wald` assumes asymptotic normality of a linear contrast
(`hAN`); deriving that contrast form from this theorem is not done here.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory Filter Finset

open scoped Function RealInnerProductSpace Topology

namespace MathlibExt.Probability.Statistics.LinearModel

/-- The population score second-moment matrix, entrywise:
`Ω a b = 𝔼[(x₀ u₀) a * (x₀ u₀) b]`. Under the exogeneity hypothesis
`𝔼[x₀ u₀] = 0` this is the covariance matrix of the score `x₀ u₀`, the
meat of the sandwich covariance `Q⁻¹ Ω Q⁻¹`. It equals the population HC0 meat
`hc0PopMeat` (`popScoreCov_eq_hc0PopMeat`); the frozen ST05.T02 statement keeps this name. -/
noncomputable def popScoreCov {k : Type*} [Fintype k] {Ω : Type*} [MeasurableSpace Ω]
    (X0 : Ω → (k → ℝ)) (U0 : Ω → ℝ) (μ : Measure Ω) : Matrix k k ℝ :=
  Matrix.of fun a b => ∫ ω, ((U0 ω) • X0 ω) a * ((U0 ω) • X0 ω) b ∂μ

/-! ### Proof steps -/

private lemma popScoreCov_posSemidef {k : Type*} [Fintype k] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X0 : Ω → (k → ℝ)} {U0 : Ω → ℝ}
    (hscore2 : MemLp (fun ω => U0 ω • X0 ω) 2 μ) :
    (popScoreCov X0 U0 μ).PosSemidef := by
  have hcoord : ∀ a, MemLp (fun ω => (U0 ω • X0 ω) a) 2 μ := fun a =>
    hscore2.continuousLinearMap_comp
      (ContinuousLinearMap.proj a : (k → ℝ) →L[ℝ] ℝ)
  have hint : ∀ a b,
      Integrable (fun ω => (U0 ω • X0 ω) a * (U0 ω • X0 ω) b) μ :=
    fun a b => (hcoord a).integrable_mul (hcoord b)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (popScoreCov X0 U0 μ)ᴴ = popScoreCov X0 U0 μ
    ext a b
    simp only [Matrix.conjTranspose_apply, popScoreCov, Matrix.of_apply,
      star_trivial]
    apply integral_congr_ae
    filter_upwards with ω
    exact mul_comm _ _
  · intro x
    have hterm : ∀ i j : k, x i * (popScoreCov X0 U0 μ i j * x j)
        = ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ := by
      intro i j
      have hC : (x i * x j) * (∫ ω, (U0 ω • X0 ω) i * (U0 ω • X0 ω) j ∂μ)
          = ∫ ω, (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) ∂μ :=
        (integral_const_mul _ _).symm
      have hL : x i * (popScoreCov X0 U0 μ i j * x j)
          = (x i * x j) * (∫ ω, (U0 ω • X0 ω) i * (U0 ω • X0 ω) j ∂μ) := by
        simp only [popScoreCov, Matrix.of_apply]
        ring
      have hR : (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j))
          = fun ω => (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) := by
        funext ω
        ring
      rw [hL, hR, ← hC]
    have hsq : ∀ ω : Ω, (∑ i, x i * (U0 ω • X0 ω) i) ^ 2
        = ∑ i, ∑ j, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have htermInt : ∀ i j : k,
        Integrable
          (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j)) μ := by
      intro i j
      have hEq : (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j))
          = fun ω => (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) := by
        funext ω
        ring
      rw [hEq]
      exact (hint i j).const_mul _
    have hquad : star x ⬝ᵥ popScoreCov X0 U0 μ *ᵥ x
        = ∫ ω, (∑ i, x i * (U0 ω • X0 ω) i) ^ 2 ∂μ := by
      rw [star_trivial]
      have h1 : x ⬝ᵥ popScoreCov X0 U0 μ *ᵥ x
          = ∑ i, ∑ j, x i * (popScoreCov X0 U0 μ i j * x j) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [h1]
      have h2 : (∑ i, ∑ j, x i * (popScoreCov X0 U0 μ i j * x j))
          = ∑ i, ∑ j,
            ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      rw [h2]
      have h3 : (∑ i, ∑ j,
          ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ)
          = ∫ ω, ∑ i, ∑ j,
            x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ := by
        refine Eq.trans ?_ (integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ fun j _ => htermInt i j)).symm
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (integral_finsetSum Finset.univ (fun j _ => htermInt i j)).symm
      rw [h3]
      congr 1
      ext ω
      exact (hsq ω).symm
    rw [hquad]
    exact integral_nonneg fun ω => sq_nonneg _

private lemma variance_inner_score {k : Type*} [Fintype k] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X0 : Ω → (k → ℝ)} {U0 : Ω → ℝ}
    (hmeanScore : ∫ ω, U0 ω • X0 ω ∂μ = 0) (hscore2 : MemLp (fun ω => U0 ω • X0 ω) 2 μ)
    (t : EuclideanSpace ℝ k) :
    Var[fun ω => ⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫; μ] =
      WithLp.ofLp t ⬝ᵥ popScoreCov X0 U0 μ *ᵥ WithLp.ofLp t := by
  have hcoord : ∀ a, MemLp (fun ω => (U0 ω • X0 ω) a) 2 μ := fun a =>
    hscore2.continuousLinearMap_comp
      (ContinuousLinearMap.proj a : (k → ℝ) →L[ℝ] ℝ)
  have hint : ∀ a b,
      Integrable (fun ω => (U0 ω • X0 ω) a * (U0 ω • X0 ω) b) μ :=
    fun a b => (hcoord a).integrable_mul (hcoord b)
  have hs_int : Integrable (fun ω => U0 ω • X0 ω) μ :=
    hscore2.integrable (one_le_two : (1 : ENNReal) ≤ 2)
  have hinner : ∀ ω : Ω, ⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫
      = ∑ a, (U0 ω • X0 ω) a * WithLp.ofLp t a := by
    intro ω
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact mul_comm _ _
  have htermMean : ∀ a,
      Integrable (fun ω => (U0 ω • X0 ω) a * WithLp.ofLp t a) μ := by
    intro a
    have hEq : (fun ω => (U0 ω • X0 ω) a * WithLp.ofLp t a)
        = fun ω => WithLp.ofLp t a * (U0 ω • X0 ω) a := by
      funext ω
      exact mul_comm _ _
    rw [hEq]
    exact ((hcoord a).integrable (one_le_two : (1 : ENNReal) ≤ 2)).const_mul _
  have hterm0 : ∀ a, (∫ ω, (U0 ω • X0 ω) a * WithLp.ofLp t a ∂μ) = 0 := by
    intro a
    have h0 : (∫ ω, (U0 ω • X0 ω) a ∂μ) = 0 := by
      let L : (k → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
      have hcomm := ContinuousLinearMap.integral_comp_comm L hs_int
      have hEq : (fun ω => (U0 ω • X0 ω) a) = fun ω => L (U0 ω • X0 ω) := by
        funext ω
        exact (ContinuousLinearMap.proj_apply a _).symm
      rw [hEq, hcomm, hmeanScore, map_zero]
    have hfactor : (∫ ω, (U0 ω • X0 ω) a * WithLp.ofLp t a ∂μ)
        = (∫ ω, (U0 ω • X0 ω) a ∂μ) * WithLp.ofLp t a := by
      have hEq : (fun ω => (U0 ω • X0 ω) a * WithLp.ofLp t a)
          = fun ω => WithLp.ofLp t a * (U0 ω • X0 ω) a := by
        funext ω
        exact mul_comm _ _
      rw [hEq, integral_const_mul, mul_comm]
    rw [hfactor, h0, zero_mul]
  have hmean : (∫ ω, ⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫ ∂μ) = 0 := by
    have hfun : (fun ω => ⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫)
        = fun ω => ∑ a, (U0 ω • X0 ω) a * WithLp.ofLp t a := funext hinner
    rw [hfun, integral_finsetSum Finset.univ (fun a _ => htermMean a)]
    exact Finset.sum_eq_zero fun a _ => hterm0 a
  have hX_ae : AEMeasurable (fun ω => ⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫) μ := by
    have hsum : Integrable
        (fun ω => ∑ a, (U0 ω • X0 ω) a * WithLp.ofLp t a) μ :=
      integrable_finsetSum Finset.univ fun a _ => htermMean a
    exact (hsum.congr (Eventually.of_forall fun ω => (hinner ω).symm)).aemeasurable
  rw [variance_of_integral_eq_zero hX_ae hmean]
  have h2 : (fun ω => (⟪WithLp.toLp 2 (U0 ω • X0 ω), t⟫) ^ 2)
      = fun ω => (∑ a, (U0 ω • X0 ω) a * WithLp.ofLp t a) ^ 2 := by
    funext ω
    rw [hinner]
  rw [h2]
  have hquad : ∀ x : k → ℝ, x ⬝ᵥ popScoreCov X0 U0 μ *ᵥ x
      = ∫ ω, (∑ a, (U0 ω • X0 ω) a * x a) ^ 2 ∂μ := by
    intro x
    have hterm : ∀ i j : k, x i * (popScoreCov X0 U0 μ i j * x j)
        = ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ := by
      intro i j
      have hC : (x i * x j) * (∫ ω, (U0 ω • X0 ω) i * (U0 ω • X0 ω) j ∂μ)
          = ∫ ω, (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) ∂μ :=
        (integral_const_mul _ _).symm
      have hL : x i * (popScoreCov X0 U0 μ i j * x j)
          = (x i * x j) * (∫ ω, (U0 ω • X0 ω) i * (U0 ω • X0 ω) j ∂μ) := by
        simp only [popScoreCov, Matrix.of_apply]
        ring
      have hR : (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j))
          = fun ω => (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) := by
        funext ω
        ring
      rw [hL, hR, ← hC]
    have hsq : ∀ ω : Ω, (∑ a, (U0 ω • X0 ω) a * x a) ^ 2
        = ∑ i, ∑ j, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have htermInt : ∀ i j : k,
        Integrable
          (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j)) μ := by
      intro i j
      have hEq : (fun ω => x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j))
          = fun ω => (x i * x j) * ((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) := by
        funext ω
        ring
      rw [hEq]
      exact (hint i j).const_mul _
    have h1 : x ⬝ᵥ popScoreCov X0 U0 μ *ᵥ x
        = ∑ i, ∑ j, x i * (popScoreCov X0 U0 μ i j * x j) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [h1]
    have h2q : (∑ i, ∑ j, x i * (popScoreCov X0 U0 μ i j * x j))
        = ∑ i, ∑ j,
          ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    rw [h2q]
    have h3 : (∑ i, ∑ j,
        ∫ ω, x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ)
        = ∫ ω, ∑ i, ∑ j,
          x i * (((U0 ω • X0 ω) i * (U0 ω • X0 ω) j) * x j) ∂μ := by
      refine Eq.trans ?_ (integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ fun j _ => htermInt i j)).symm
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (integral_finsetSum Finset.univ (fun j _ => htermInt i j)).symm
    rw [h3]
    congr 1
    ext ω
    exact (hsq ω).symm
  exact (hquad (WithLp.ofLp t)).symm

private lemma hasLaw_inner_multivariateGaussian_zero {k : Type*} [Fintype k] [DecidableEq k]
    {M : Matrix k k ℝ} (hM : M.PosSemidef) (t : EuclideanSpace ℝ k) :
    HasLaw (fun x : EuclideanSpace ℝ k => ⟪x, t⟫)
      (gaussianReal 0 (WithLp.ofLp t ⬝ᵥ M *ᵥ WithLp.ofLp t).toNNReal)
      (multivariateGaussian 0 M) := by
  have hfun : (fun x : EuclideanSpace ℝ k => ⟪x, t⟫) = ⇑(innerSL ℝ t) := by
    funext x
    exact ((real_inner_comm t x).trans (innerSL_apply_apply ℝ t x).symm)
  have hmem : MemLp (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ k) M) :=
    IsGaussian.memLp_two_id
  have hmean : (∫ x, (innerSL ℝ t) x
      ∂multivariateGaussian (0 : EuclideanSpace ℝ k) M) = 0 := by
    have hid_int : Integrable (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) M) :=
      hmem.integrable (one_le_two : (1 : ENNReal) ≤ 2)
    have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ t) hid_int
    have hid0 : (∫ x, id x ∂multivariateGaussian (0 : EuclideanSpace ℝ k) M) = 0 :=
      integral_id_multivariateGaussian
    calc (∫ x, (innerSL ℝ t) x ∂multivariateGaussian (0 : EuclideanSpace ℝ k) M)
        = (innerSL ℝ t)
          (∫ x, id x ∂multivariateGaussian (0 : EuclideanSpace ℝ k) M) := hcomm
      _ = 0 := by rw [hid0, map_zero]
  have hvar : Var[⇑(innerSL ℝ t);
      multivariateGaussian (0 : EuclideanSpace ℝ k) M]
      = WithLp.ofLp t ⬝ᵥ M *ᵥ WithLp.ofLp t := by
    have hself := covarianceBilin_self hmem t
    have hcov := covarianceBilin_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ k)) hM t t
    have hVX : (⇑(innerSL ℝ t) : EuclideanSpace ℝ k → ℝ) = fun u => ⟪t, u⟫ := by
      funext u
      exact innerSL_apply_apply ℝ t u
    rw [hVX, ← hself, hcov]
  have hmap : Measure.map ⇑(innerSL ℝ t)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) M)
      = gaussianReal (∫ x, ⇑(innerSL ℝ t) x
          ∂multivariateGaussian (0 : EuclideanSpace ℝ k) M)
        Var[⇑(innerSL ℝ t);
          multivariateGaussian (0 : EuclideanSpace ℝ k) M].toNNReal :=
    IsGaussian.map_eq_gaussianReal
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ k) M) (innerSL ℝ t)
  rw [hfun]
  rw [hmean, hvar] at hmap
  refine ⟨?_, hmap⟩
  exact (innerSL ℝ t).continuous.aemeasurable

private lemma tendstoInDistribution_sqrt_smul_mean_score {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintScore : Integrable (fun ω => U 0 ω • X 0 ω) μ)
    (hmeanScore : ∫ ω, U 0 ω • X 0 ω ∂μ = 0)
    (hscore2 : MemLp (fun ω => U 0 ω • X 0 ω) 2 μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω)))
      atTop (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k) (fun _ => μ)
      (multivariateGaussian 0 (popScoreCov (X 0) (U 0) μ)) := by
  let L : (k → ℝ) →L[ℝ] EuclideanSpace ℝ k :=
    LinearMap.toContinuousLinearMap (EuclideanSpace.equiv k ℝ).symm.toLinearMap
  have hX : MemLp (fun ω => WithLp.toLp 2 (U 0 ω • X 0 ω)) 2 μ :=
    L.comp_memLp' hscore2
  have hmean0 : (∫ ω, WithLp.toLp 2 (U 0 ω • X 0 ω) ∂μ) = 0 := by
    have hcomm := ContinuousLinearMap.integral_comp_comm L hintScore
    have hEq : (fun ω => WithLp.toLp 2 (U 0 ω • X 0 ω))
        = fun ω => L (U 0 ω • X 0 ω) := rfl
    rw [hEq, hcomm, hmeanScore, map_zero]
  have hg_meas : Measurable
      (fun p : (k → ℝ) × ℝ => WithLp.toLp 2 (p.2 • p.1)) := by
    fun_prop
  have hindep' : iIndepFun (fun i ω => WithLp.toLp 2 (U i ω • X i ω)) μ :=
    hindep.comp (fun _ p => WithLp.toLp 2 (p.2 • p.1)) (fun _ => hg_meas)
  have hident' : ∀ i, IdentDistrib (fun ω => WithLp.toLp 2 (U i ω • X i ω))
      (fun ω => WithLp.toLp 2 (U 0 ω • X 0 ω)) μ μ :=
    fun i => (hident i).comp hg_meas
  have hYlaw : ∀ t : EuclideanSpace ℝ k,
      HasLaw (fun ω ↦ ⟪(id : EuclideanSpace ℝ k → EuclideanSpace ℝ k) ω, t⟫)
        (gaussianReal 0
          (Var[fun ω ↦ ⟪WithLp.toLp 2 (U 0 ω • X 0 ω), t⟫; μ]).toNNReal)
        (multivariateGaussian 0 (popScoreCov (X 0) (U 0) μ)) := by
    intro t
    have hvar := variance_inner_score hmeanScore hscore2 t
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian_zero (popScoreCov_posSemidef hscore2) t
  have hCLT := tendstoInDistribution_inv_sqrt_smul_sum_sub
    (X := fun i ω => WithLp.toLp 2 (U i ω • X i ω))
    (Y := (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k))
    (P := μ) (P' := multivariateGaussian 0 (popScoreCov (X 0) (U 0) μ))
    aemeasurable_id hYlaw hX hindep' hident'
  have hseq : (fun (n : ℕ) ω ↦ (√n)⁻¹ •
        (∑ k ∈ range n, WithLp.toLp 2 (U k ω • X k ω)
          - n • ∫ ω, WithLp.toLp 2 (U 0 ω • X 0 ω) ∂μ))
      = (fun (n : ℕ) ω => √(n : ℝ) •
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω))) := by
    funext n ω
    rw [hmean0, nsmul_zero, sub_zero]
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      have hsqrt_ne : √(n : ℝ) ≠ 0 := by
        intro h
        apply hn
        calc (n : ℝ) = √(n : ℝ) * √(n : ℝ) :=
              (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
          _ = 0 := by rw [h, zero_mul]
      have hsq : √(n : ℝ) * √(n : ℝ) = n :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      have key : (√(n : ℝ))⁻¹ = √(n : ℝ) * (n : ℝ)⁻¹ := by
        calc (√(n : ℝ))⁻¹ = (√(n : ℝ))⁻¹ * 1 := (mul_one _).symm
          _ = (√(n : ℝ))⁻¹ * (√(n : ℝ) * √(n : ℝ) * (n : ℝ)⁻¹) := by
            congr 1
            rw [hsq, mul_inv_cancel₀ hn]
          _ = √(n : ℝ) * (n : ℝ)⁻¹ := by
            rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
      rw [smul_smul, key]
  rw [← hseq]
  exact hCLT

private lemma aemeasurable_sampleGram_inv {k : Type*} [Fintype k] [DecidableEq k] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (n : ℕ) :
    AEMeasurable (fun ω => fun a b =>
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i =>
    measurable_fst.comp_aemeasurable (hident i).aemeasurable_fst
  have hCoord : ∀ i a, AEMeasurable (fun ω => X i ω a) μ :=
    fun i a => (measurable_pi_apply a).comp_aemeasurable (hX i)
  have hProd : ∀ i a b,
      AEMeasurable (fun ω => X i ω a * X i ω b) μ :=
    fun i a b => (hCoord i a).mul (hCoord i b)
  have hSum : ∀ a b, AEMeasurable
      (fun ω => ∑ i ∈ Finset.range n, X i ω a * X i ω b) μ :=
    fun a b => Finset.aemeasurable_fun_sum (Finset.range n)
      fun i _ => hProd i a b
  have hEqGram : ∀ ω a b,
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) a b =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω a * X i ω b :=
    fun ω a b => by
      simp only [Matrix.smul_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, smul_eq_mul]
  have hEntry : ∀ a b, AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) a b) μ := fun a b => by
    have hEqFun :
        (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)) a b) =
        (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          X i ω a * X i ω b) :=
      funext fun ω => hEqGram ω a b
    rw [hEqFun]
    exact aemeasurable_const.mul (hSum a b)
  have hGram : AEMeasurable
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) μ :=
    aemeasurable_pi_iff.mpr fun a =>
      aemeasurable_pi_iff.mpr fun b => hEntry a b
  have hDetMeas : Measurable (fun A : Matrix k k ℝ => A.det) := by
    fun_prop
  have hDet : AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det) μ :=
    hDetMeas.comp_aemeasurable hGram
  have hDetInv : AEMeasurable
      (fun ω => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det)⁻¹) μ :=
    hDet.inv
  have hAdjMeas : Measurable (fun A : Matrix k k ℝ => A.adjugate) := by
    fun_prop
  have hAdj : AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).adjugate) μ :=
    hAdjMeas.comp_aemeasurable hGram
  have hAdjEntry : ∀ a b, AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).adjugate a b) μ :=
    fun a b => (measurable_pi_apply b).comp_aemeasurable
      ((measurable_pi_apply a).comp_aemeasurable hAdj)
  have hEqInv : ∀ ω a b,
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b =
        (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)).det)⁻¹ *
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)).adjugate a b :=
    fun ω a b => by
      rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
        smul_eq_mul]
  have hInvEntry : ∀ a b, AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ :=
    fun a b => by
      have hEqFun :
          (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) =
          (fun ω => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (X i ω) (X i ω)).det)⁻¹ *
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (X i ω) (X i ω)).adjugate a b) :=
        funext fun ω => hEqInv ω a b
      rw [hEqFun]
      exact hDetInv.mul (hAdjEntry a b)
  exact aemeasurable_pi_iff.mpr fun a =>
    aemeasurable_pi_iff.mpr fun b => hInvEntry a b

private lemma tendstoInMeasure_sampleGram_inv {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    TendstoInMeasure μ (fun (n : ℕ) ω => fun a b =>
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b)
      atTop (fun _ => fun a b => (popGram (X 0) μ)⁻¹ a b) := by
  have hindepX : iIndepFun X μ :=
    hindep.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hidentX : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i => (hident i).comp measurable_fst
  have hPair : Pairwise ((· ⟂ᵢ[μ] ·) on X) :=
    fun i j hij => hindepX.indepFun hij
  have hAe := tendsto_sampleGram_ae hPair hidentX hintGram
  have hDetNe : (popGram (X 0) μ).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  have hRing : ContinuousAt Ring.inverse (popGram (X 0) μ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hDetNe
  have hCont : ContinuousAt Inv.inv (popGram (X 0) μ) :=
    continuousAt_matrix_inv _ hRing
  have hAeInv : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹)
      atTop (𝓝 (popGram (X 0) μ)⁻¹) :=
    hAe.mono fun ω hω => hCont.tendsto.comp hω
  have hMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => fun a b => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ :=
    fun n => (aemeasurable_sampleGram_inv hident n).aestronglyMeasurable
  have hAeInvFun : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => fun a b => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b)
      atTop (𝓝 (fun a b => (popGram (X 0) μ)⁻¹ a b)) := by
    filter_upwards [hAeInv] with ω hω
    refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hω a) b
  exact tendstoInMeasure_of_tendsto_ae hMeas hAeInvFun

private lemma tendsto_measure_not_isUnit_sampleGram {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    Tendsto (fun n : ℕ => μ {ω | ¬IsUnit
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))}) atTop (𝓝 0) := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i =>
    measurable_fst.comp_aemeasurable (hident i).aemeasurable_fst
  have hCoord : ∀ i a, AEMeasurable (fun ω => X i ω a) μ :=
    fun i a => (measurable_pi_apply a).comp_aemeasurable (hX i)
  have hProd : ∀ i a b, AEMeasurable (fun ω => X i ω a * X i ω b) μ :=
    fun i a b => (hCoord i a).mul (hCoord i b)
  have hindepX : iIndepFun X μ :=
    hindep.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hidentX : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i => (hident i).comp measurable_fst
  have hPair : Pairwise ((· ⟂ᵢ[μ] ·) on X) :=
    fun i j hij => hindepX.indepFun hij
  have hAe := tendsto_sampleGram_ae hPair hidentX hintGram
  have hDetNe : (popGram (X 0) μ).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  have hDet : Continuous fun A : Matrix k k ℝ => A.det := continuous_id.matrix_det
  have hAeDet : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det)
      atTop (𝓝 (popGram (X 0) μ).det) :=
    hAe.mono fun ω hω => (hDet.tendsto _).comp hω
  have hMeasDet : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det) μ := fun n => by
    have hSumN : ∀ a b, AEMeasurable
        (fun ω => ∑ i ∈ Finset.range n, X i ω a * X i ω b) μ :=
      fun a b => Finset.aemeasurable_fun_sum _ (fun i _ => hProd i a b)
    have hEqGramN : ∀ ω a b,
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)) a b =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω a * X i ω b := by
      intro ω a b
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        Matrix.vecMulVec_apply]
    have hEntryN : ∀ a b, AEMeasurable
        (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)) a b) μ := by
      intro a b
      have hEqFun :
          (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (X i ω) (X i ω)) a b) =
            (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω a * X i ω b) :=
        funext fun ω => hEqGramN ω a b
      rw [hEqFun]
      exact aemeasurable_const.mul (hSumN a b)
    have hGramN : AEMeasurable
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)) μ :=
      aemeasurable_pi_iff.mpr fun a => aemeasurable_pi_iff.mpr fun b => hEntryN a b
    have hDetMeas : Measurable (fun A : Matrix k k ℝ => A.det) := by fun_prop
    exact (hDetMeas.comp_aemeasurable hGramN).aestronglyMeasurable
  have hInMeasDet : TendstoInMeasure μ
      (fun (n : ℕ) ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det)
      atTop (fun _ => (popGram (X 0) μ).det) :=
    tendstoInMeasure_of_tendsto_ae hMeasDet hAeDet
  have hEpsNe : edist (0 : ℝ) (popGram (X 0) μ).det ≠ 0 := by
    intro hZero
    rw [edist_eq_zero] at hZero
    exact hDetNe hZero.symm
  have hEpsPos : 0 < edist (0 : ℝ) (popGram (X 0) μ).det :=
    lt_of_le_of_ne zero_le (Ne.symm hEpsNe)
  have hTop : Tendsto
      (fun n : ℕ => μ {ω | edist (0 : ℝ) (popGram (X 0) μ).det ≤
        edist (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)).det)
          (popGram (X 0) μ).det}) atTop (𝓝 0) :=
    hInMeasDet _ hEpsPos
  have hSubUnit : ∀ n : ℕ,
      {ω | ¬IsUnit ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))} ⊆
      {ω | (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det) = 0} := by
    intro n ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    by_contra hNe
    exact h ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hNe))
  have hSubDet : ∀ n : ℕ,
      {ω | (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)).det) = 0} ⊆
      {ω | edist (0 : ℝ) (popGram (X 0) μ).det ≤
        edist (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)).det)
          (popGram (X 0) μ).det} := by
    intro n ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    rw [h]
  have hLe : ∀ n : ℕ, μ {ω | ¬IsUnit ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (X i ω) (X i ω))} ≤
      μ {ω | edist (0 : ℝ) (popGram (X 0) μ).det ≤
        edist (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω)).det)
          (popGram (X 0) μ).det} :=
    fun n => le_trans (measure_mono (hSubUnit n)) (measure_mono (hSubDet n))
  have hZero : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hZero hTop (fun n => zero_le)
    hLe

private lemma sqrt_smul_olsSeqEstimator_sub {k : Type*} [Fintype k] [DecidableEq k] {Ω : Type*}
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ} (β : k → ℝ) (n : ℕ) (ω : Ω)
    (h : IsUnit ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))) :
    √(n : ℝ) • (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β) =
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        (√(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, U i ω • X i ω)) := by
  rw [olsSeqEstimator_eq]
  have hVec : ∀ x : k → ℝ,
      (Matrix.vecMulVec x x) *ᵥ β = (x ⬝ᵥ β) • x := fun x => by
    ext a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Matrix.vecMulVec_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hSumVec : (∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β) • X i ω) =
      (∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (hVec _).symm
  have hSmulVec : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        (X i ω ⬝ᵥ β) • X i ω) =
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β := by
    rw [hSumVec, Matrix.smul_mulVec]
  have hSplit : (∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β + U i ω) • X i ω) =
      (∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β) • X i ω) +
        (∑ i ∈ Finset.range n, U i ω • X i ω) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact add_smul _ _ _
  have hDet : IsUnit (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (X i ω) (X i ω))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h
  have hMul : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) = 1 :=
    Matrix.nonsing_inv_mul _ hDet
  have hInvMul : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
      (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β) = β := by
    calc ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
            (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
              Matrix.vecMulVec (X i ω) (X i ω)) *ᵥ β)
          = (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
              Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *
            ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
              Matrix.vecMulVec (X i ω) (X i ω))) *ᵥ β :=
            Matrix.mulVec_mulVec _ _ _
        _ = (1 : Matrix k k ℝ) *ᵥ β := by rw [hMul]
        _ = β := Matrix.one_mulVec _
  have hOlsEq : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        (X i ω ⬝ᵥ β + U i ω) • X i ω) =
      β + ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, U i ω • X i ω) := by
    rw [hSplit, smul_add, Matrix.mulVec_add]
    have hFirst : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            (X i ω ⬝ᵥ β) • X i ω) = β := by
      rw [hSmulVec]
      exact hInvMul
    rw [hFirst]
  have hSub : (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω) - β) =
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, U i ω • X i ω) := by
    rw [hOlsEq, add_sub_cancel_left]
  rw [hSub]
  exact (Matrix.mulVec_smul _ _ _).symm

private lemma s5b_eq_on_unit {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (β : k → ℝ) (n : ℕ) (ω : Ω)
    (hU : IsUnit ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (X i ω) (X i ω))) :
    WithLp.toLp 2 (√(n : ℝ) • (olsSeqEstimator X
        (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β)) =
      WithLp.toLp 2 (Matrix.of (fun a b => ((n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) *ᵥ
        WithLp.ofLp (√(n : ℝ) • ((n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω)))) := by
  have hSqrt := sqrt_smul_olsSeqEstimator_sub (U := U) β n ω hU
  have hOf : WithLp.ofLp (√(n : ℝ) • ((n : ℝ)⁻¹ •
      ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω))) =
      √(n : ℝ) • ((n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, U i ω • X i ω) := by
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sum]
  have hMat : Matrix.of (fun a b => ((n : ℝ)⁻¹ •
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) =
      ((n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ := rfl
  rw [hSqrt, hMat, hOf]

private lemma tendstoInMeasure_ols_sub_approx {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ} (β : k → ℝ)
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    TendstoInMeasure μ
      ((fun (n : ℕ) ω => WithLp.toLp 2 ((√(n : ℝ)) •
          (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β))) -
        (fun (n : ℕ) ω => WithLp.toLp 2 (Matrix.of (fun a b =>
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) *ᵥ
          WithLp.ofLp (√(n : ℝ) •
            ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω))))))
      atTop 0 := by
  have hNotUnit := tendsto_measure_not_isUnit_sampleGram
    hindep hident hintGram hQ
  set qhat : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (X i ω) (X i ω) with hqhat
  set fseq : ℕ → Ω → WithLp 2 (k → ℝ) := fun n ω =>
    WithLp.toLp 2 (√(n : ℝ) • (olsSeqEstimator X
      (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β)) with hfseq
  set gseq : ℕ → Ω → WithLp 2 (k → ℝ) := fun n ω =>
    WithLp.toLp 2 (Matrix.of (fun a b => (qhat n ω)⁻¹ a b) *ᵥ
      WithLp.ofLp (√(n : ℝ) • ((n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, WithLp.toLp 2 (U i ω • X i ω)))) with hgseq
  intro ε hε
  have hSub : ∀ n : ℕ, {ω | ε ≤ edist ((fseq - gseq) n ω) 0} ⊆
      {ω | ¬IsUnit (qhat n ω)} := by
    intro n ω hmem
    simp only [Set.mem_ofPred_eq] at hmem ⊢
    intro hU
    have hU' : IsUnit ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω)) := by
      simpa [hqhat] using hU
    have hFG : fseq n ω = gseq n ω := by
      simp only [hfseq, hgseq, hqhat]
      exact s5b_eq_on_unit β n ω hU'
    have hZero : (fseq - gseq) n ω = 0 := by
      simp only [Pi.sub_apply, hFG, sub_self]
    rw [hZero, edist_self] at hmem
    exact (not_le_of_gt hε) hmem
  have hLe : (fun n : ℕ => μ {ω | ε ≤ edist ((fseq - gseq) n ω) 0}) ≤
      (fun n : ℕ => μ {ω | ¬IsUnit (qhat n ω)}) :=
    fun n => measure_mono (hSub n)
  have hZero : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0) :=
    tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hZero hNotUnit
    (fun n => bot_le) hLe

private lemma aemeasurable_sqrt_smul_olsSeqEstimator_sub {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (n : ℕ) :
    AEMeasurable (fun ω => WithLp.toLp 2 ((√(n : ℝ)) •
      (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β))) μ := by
  have hInv : AEMeasurable (fun ω => fun a b =>
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ :=
    aemeasurable_sampleGram_inv hident n
  have hInvEntry : ∀ a b, AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ :=
    fun a b => (measurable_pi_apply b).comp_aemeasurable
      ((measurable_pi_apply a).comp_aemeasurable hInv)
  have hX : ∀ i, AEMeasurable (X i) μ := fun i =>
    measurable_fst.comp_aemeasurable (hident i).aemeasurable_fst
  have hU : ∀ i, AEMeasurable (fun ω => U i ω) μ := fun i =>
    measurable_snd.comp_aemeasurable (hident i).aemeasurable_fst
  have hXCoord : ∀ i a, AEMeasurable (fun ω => X i ω a) μ :=
    fun i a => (measurable_pi_apply a).comp_aemeasurable (hX i)
  have hDot : ∀ i, AEMeasurable (fun ω => X i ω ⬝ᵥ β) μ := fun i => by
    have hEq : (fun ω => X i ω ⬝ᵥ β) = (fun ω => ∑ a, X i ω a * β a) := rfl
    rw [hEq]
    exact Finset.aemeasurable_fun_sum Finset.univ fun a _ =>
      (hXCoord i a).mul aemeasurable_const
  have hY : ∀ i, AEMeasurable (fun ω => X i ω ⬝ᵥ β + U i ω) μ :=
    fun i => (hDot i).add (hU i)
  have hYX : ∀ i a, AEMeasurable
      (fun ω => (X i ω ⬝ᵥ β + U i ω) * X i ω a) μ :=
    fun i a => (hY i).mul (hXCoord i a)
  have hSumYX : ∀ a, AEMeasurable
      (fun ω => ∑ i ∈ Finset.range n, (X i ω ⬝ᵥ β + U i ω) * X i ω a) μ :=
    fun a => Finset.aemeasurable_fun_sum (Finset.range n) fun i _ => hYX i a
  have hScoreEntry : ∀ a, AEMeasurable
      (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        (X i ω ⬝ᵥ β + U i ω) • X i ω) a) μ := fun a => by
    have hEqFun :
        (fun ω => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω) a) =
        (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) * X i ω a) := by
      funext ω
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [hEqFun]
    exact aemeasurable_const.mul (hSumYX a)
  have hOlsEntry : ∀ a, AEMeasurable
      (fun ω => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) a) μ := fun a => by
    have hEq : (fun ω => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) a) =
        (fun ω => ∑ b, (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) *
          (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            (X i ω ⬝ᵥ β + U i ω) • X i ω) b)) := rfl
    rw [hEq]
    exact Finset.aemeasurable_fun_sum Finset.univ fun b _ =>
      (hInvEntry a b).mul (hScoreEntry b)
  have hSubEntry : ∀ a, AEMeasurable
      (fun ω => ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β) a) μ := fun a => by
    have hEq : (fun ω => ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β) a) =
        (fun ω => (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            (X i ω ⬝ᵥ β + U i ω) • X i ω)) a - β a) := rfl
    rw [hEq]
    exact (hOlsEntry a).sub aemeasurable_const
  have hSmulEntry : ∀ a, AEMeasurable
      (fun ω => (√(n : ℝ) • ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β)) a) μ := fun a => by
    have hEq : (fun ω => (√(n : ℝ) • ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β)) a) =
        (fun ω => √(n : ℝ) * (((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
          ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
            (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β) a)) := rfl
    rw [hEq]
    exact aemeasurable_const.mul (hSubEntry a)
  have hInner : AEMeasurable (fun ω => √(n : ℝ) • ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β)) μ :=
    aemeasurable_pi_iff.mpr hSmulEntry
  have hEqFun : (fun ω => WithLp.toLp 2 ((√(n : ℝ)) •
      (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β))) =
      (fun ω => WithLp.toLp 2 (√(n : ℝ) • ((((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
          (X i ω ⬝ᵥ β + U i ω) • X i ω)) - β))) := by
    funext ω
    rw [olsSeqEstimator_eq]
  rw [hEqFun]
  have hCont : Continuous (WithLp.toLp 2 : (k → ℝ) → WithLp 2 (k → ℝ)) := by fun_prop
  exact hCont.measurable.comp_aemeasurable hInner

private lemma map_mulVec_inv_multivariateGaussian {k : Type*} [Fintype k] [DecidableEq k]
    {Q M : Matrix k k ℝ} (hQ : Qᵀ = Q) (hM : M.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ k) M).map
        (fun v => WithLp.toLp 2 (Q⁻¹ *ᵥ WithLp.ofLp v)) =
      multivariateGaussian 0 (Q⁻¹ * M * Q⁻¹) := by
  have hFun : (fun v => WithLp.toLp 2 (Q⁻¹ *ᵥ WithLp.ofLp v)) =
      ⇑(toEuclideanLin (Q⁻¹)) := rfl
  have hT : (Q⁻¹)ᵀ = Q⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQ]
  have hZero : toEuclideanLin (Q⁻¹) (0 : EuclideanSpace ℝ k) = 0 :=
    map_zero _
  rw [hFun]
  have hMap := MetaMathlibExt.map_toEuclideanLin_multivariateGaussian
    (Q⁻¹) (0 : EuclideanSpace ℝ k) hM
  rw [hZero, hT] at hMap
  exact hMap

/-- **Asymptotic normality of OLS**: under the ST05.T01 hypotheses plus
square-integrability of the score, the OLS sequence computed from the
observed responses `yᵢ = xᵢ ⬝ᵥ β + uᵢ` satisfies: `√n (β̂ₙ - β)` converges in
distribution to `N(0, Q⁻¹ Ω Q⁻¹)`. -/
theorem tendstoInDistribution_sqrt_mul_olsSeqEstimator_sub
    {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ} (β : k → ℝ)
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω))
      (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hintScore : Integrable (fun ω => (U 0 ω) • X 0 ω) μ)
    (hmeanScore : ∫ ω, (U 0 ω) • X 0 ω ∂μ = 0)
    (hscore2 : MemLp (fun ω => (U 0 ω) • X 0 ω) 2 μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => WithLp.toLp 2 ((√(n : ℝ)) •
        (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β)))
      atTop (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k) (fun _ => μ)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        ((popGram (X 0) μ)⁻¹ * (popScoreCov (X 0) (U 0) μ) * (popGram (X 0) μ)⁻¹)) := by
  have hg : Continuous (fun p : EuclideanSpace ℝ k × (k → k → ℝ) =>
      WithLp.toLp 2 (Matrix.of p.2 *ᵥ WithLp.ofLp p.1)) := by
    fun_prop
  have hXZ := tendstoInDistribution_sqrt_smul_mean_score
    hindep hident hintScore hmeanScore hscore2
  have hYtend := tendstoInMeasure_sampleGram_inv
    hindep hident hintGram hQ
  have hYmeas : ∀ (n : ℕ), AEMeasurable (fun ω => fun a b =>
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        Matrix.vecMulVec (X i ω) (X i ω))⁻¹ a b) μ :=
    fun (n : ℕ) => aemeasurable_sampleGram_inv hident n
  have hApprox :=
    MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      hg hXZ hYtend hYmeas
  have hQSymm : (popGram (X 0) μ)ᵀ = popGram (X 0) μ := by
    ext a b
    simp only [Matrix.transpose_apply, popGram, Matrix.of_apply]
    apply integral_congr_ae
    filter_upwards with ω
    exact mul_comm _ _
  have hM := popScoreCov_posSemidef hscore2
  have hMapEq := map_mulVec_inv_multivariateGaussian hQSymm hM
  have hLaw1 : HasLaw
      (fun ω : EuclideanSpace ℝ k =>
        WithLp.toLp 2 ((popGram (X 0) μ)⁻¹ *ᵥ WithLp.ofLp ω))
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        ((popGram (X 0) μ)⁻¹ * (popScoreCov (X 0) (U 0) μ) *
          (popGram (X 0) μ)⁻¹))
      (multivariateGaussian 0 (popScoreCov (X 0) (U 0) μ)) :=
    ⟨by fun_prop, hMapEq⟩
  have hLaw2 : HasLaw
      (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        ((popGram (X 0) μ)⁻¹ * (popScoreCov (X 0) (U 0) μ) *
          (popGram (X 0) μ)⁻¹))
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        ((popGram (X 0) μ)⁻¹ * (popScoreCov (X 0) (U 0) μ) *
          (popGram (X 0) μ)⁻¹)) :=
    HasLaw.id
  have hS := MeasureTheory.TendstoInDistribution.congr_hasLaw
    hApprox hLaw1 hLaw2
  have hSub := tendstoInMeasure_ols_sub_approx
    β hindep hident hintGram hQ
  have hMeas : ∀ (n : ℕ), AEMeasurable (fun ω =>
      WithLp.toLp 2 ((√(n : ℝ)) •
        (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β))) μ :=
    fun (n : ℕ) => aemeasurable_sqrt_smul_olsSeqEstimator_sub β hident n
  exact MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub _ _ hS hSub hMeas

/-! ### Relation to the HC0 sandwich of `HeteroskedasticityRobust` -/

/-- `popScoreCov` is the population HC0 meat `hc0PopMeat`. -/
theorem popScoreCov_eq_hc0PopMeat {k : Type*} [Fintype k] {Ω : Type*} [MeasurableSpace Ω]
    (X0 : Ω → (k → ℝ)) (U0 : Ω → ℝ) (μ : Measure Ω) :
    popScoreCov X0 U0 μ = hc0PopMeat X0 U0 μ := by
  ext a b
  simp only [popScoreCov, hc0PopMeat, Matrix.of_apply]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The asymptotic covariance `Q⁻¹ Ω Q⁻¹` of `√n (β̂ₙ - β)` is the population HC0 sandwich
`hc0PopSandwich`. -/
theorem popScoreCov_sandwich_eq_hc0PopSandwich {k : Type*} [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] (X0 : Ω → (k → ℝ)) (U0 : Ω → ℝ) (μ : Measure Ω) :
    (popGram X0 μ)⁻¹ * popScoreCov X0 U0 μ * (popGram X0 μ)⁻¹ = hc0PopSandwich X0 U0 μ := by
  have hsym : (popGram X0 μ)ᵀ = popGram X0 μ := by
    ext a b
    simp only [popGram, Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    funext ω
    ring
  have hinv : ((popGram X0 μ)⁻¹)ᵀ = (popGram X0 μ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  rw [hc0PopSandwich, popScoreCov_eq_hc0PopMeat, hinv]

end MathlibExt.Probability.Statistics.LinearModel
