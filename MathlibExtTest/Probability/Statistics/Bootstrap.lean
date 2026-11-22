/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Bootstrap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for bootstrap validity

* Concrete values of the empirical distribution, sample mean and sample variance, including
  the `n = 0` convention.
* Non-vacuity of the deterministic conditional CLT: the alternating data `1, -1, 1, -1, …`
  have sample means `→ 0`, plug-in variances `→ 1` and satisfy the data Lindeberg condition,
  so the bootstrap mean is conditionally asymptotically `N(0, 1)`, and the bootstrap of
  `exp(x̄)` is conditionally asymptotically `N(0, 1)` as well.
* Non-vacuity of the finite-dimensional conditional CLT in `E = ℝ`, through Cramér–Wold.
* Non-vacuity of the almost-sure theorem: iid standard Gaussian coordinates on
  `ℕ → ℝ` satisfy all of its hypotheses.
* Non-vacuity of the almost-sure vector theorems and of `bootstrap_consistent_mean` in `ℝ²`, for
  iid data with singular (rank-one) covariance, with the Gaussian limit from
  `exists_hasLaw_inner_gaussianReal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal

namespace MathlibExtTest.Probability.Statistics.Bootstrap

open ProbabilityTheory.Bootstrap
open MathlibExt.Probability.Causality (sampleMean)

/-! ### Concrete values -/

/-- The data `0, 2, …`: `x i = 2 i`. -/
def evens (i : ℕ) : ℝ := 2 * i

example : sampleMean evens (range 2) = 1 := by
  norm_num [sampleMean_range, evens, sum_range_succ]

example : empiricalVar evens 2 = 1 := by
  norm_num [empiricalVar, sampleMean_range, evens, sum_range_succ]

/-- With no data the empirical distribution is the point mass at `0` (a convention). -/
example (x : ℕ → ℝ) : empirical x 0 = Measure.dirac 0 := by simp [empirical]

/-- Integrals against `empirical evens 2` average the two atoms `0` and `2`. -/
example : ∫ y, y ^ 2 ∂empirical evens 2 = 2 := by
  rw [integral_empirical (by norm_num)]
  simp [evens, sum_range_succ]; norm_num

/-- A bootstrap draw at sample size `2` has the empirical law of `0, 2`. -/
example : (world evens).map (fun ω => ω 2 5) = empirical evens 2 :=
  (measurePreserving_world_eval evens 2 5).map_eq

/-- The positive empirical rows are the canonical resampling laws. -/
example (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) : empirical x n = empiricalLaw x n :=
  empirical_eq_empiricalLaw hn.ne'

example (x : ℕ → ℝ) (n : ℕ) : sampleMean x (range n) = empiricalMean x n :=
  sampleMean_eq_empiricalMean x n

example (ω : ℕ → ℕ → ℝ) (n : ℕ) : bootMean n ω = empiricalMean (ω n) n :=
  bootMean_eq_empiricalMean n ω

/-- The zero-row conventions remain distinct for data starting away from zero. -/
example : (world (fun _ => (2 : ℝ))).map (fun ω => ω 0 5) = Measure.dirac 0 := by
  rw [(measurePreserving_world_eval _ 0 5).map_eq]
  simp [empirical]

example : (bootstrapMeasure (fun _ => (2 : ℝ))).map (fun ω => ω 0 5) = Measure.dirac 2 := by
  rw [(measurePreserving_bootstrap_coord _ 0 5).map_eq]
  simp [empiricalLaw_eq]

/-- The coupling bridge changes only the unused row zero. -/
example (x : ℕ → ℝ) :
    (world x).map (fun ω n k => if n = 0 then x 0 else ω n k) = bootstrapMeasure x :=
  map_world_bootstrapMeasure x

/-! ### Non-vacuity: alternating data -/

/-- The alternating data `1, -1, 1, -1, …`. -/
def alt (i : ℕ) : ℝ := (-1) ^ i

theorem alt_sq (i : ℕ) : alt i ^ 2 = 1 := by
  simp [alt, ← pow_mul]

theorem tendsto_sampleMean_alt : Tendsto (fun n : ℕ => sampleMean alt (range n)) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, |∑ i ∈ range n, alt i| ≤ 1 := by
    intro n
    have h := geom_sum_eq (x := (-1 : ℝ)) (by norm_num) n
    simp only [alt, h]
    rcases neg_one_pow_eq_or ℝ n with h1 | h1 <;> rw [h1] <;> norm_num
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n => ?_) hinv
  rw [sampleMean_range, norm_mul, norm_inv, Real.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖∑ i ∈ range n, alt i‖ ≤ (n : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (hbound n) (by positivity)
    _ = (n : ℝ)⁻¹ := mul_one _

theorem tendsto_meanSq_alt :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, alt i ^ 2) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [alt_sq, hn']

theorem tendsto_empiricalVar_alt : Tendsto (empiricalVar alt) atTop (𝓝 ((1 : ℝ≥0) : ℝ)) := by
  simpa using tendsto_empiricalVar tendsto_sampleMean_alt tendsto_meanSq_alt

/-- The bootstrap mean of the alternating data is conditionally asymptotically `N(0, 1)`. -/
example : TendstoInDistribution
    (fun (n : ℕ) ω => √(n : ℝ) * (bootMean n ω - sampleMean alt (range n))) atTop (id : ℝ → ℝ)
    (fun _ => world alt) (gaussianReal 0 1) :=
  tendstoInDistribution_bootMean alt tendsto_empiricalVar_alt
    (lindeberg_of_tendsto_sampleMean tendsto_sampleMean_alt tendsto_meanSq_alt)

/-- The bootstrap of the smooth statistic `exp(x̄)` for the alternating data: the derivative of
`exp` at the limit mean `0` is `1`, so the limit is `N(0, 1² · 1) = N(0, 1)`. -/
example : TendstoInDistribution
    (fun (n : ℕ) ω => √(n : ℝ) * (Real.exp (bootMean n ω) - Real.exp (sampleMean alt (range n))))
    atTop (id : ℝ → ℝ) (fun _ => world alt) (gaussianReal 0 1) := by
  have h := tendstoInDistribution_bootstrap_of_hasStrictDerivAt alt tendsto_empiricalVar_alt
    (lindeberg_of_tendsto_sampleMean tendsto_sampleMean_alt tendsto_meanSq_alt)
    tendsto_sampleMean_alt (Real.hasStrictDerivAt_exp 0) Real.measurable_exp
  have hv : ‖Real.exp 0‖₊ ^ 2 * (1 : ℝ≥0) = 1 := by simp
  rwa [hv] at h

/-! ### Non-vacuity of the finite-dimensional theorems (`E = ℝ`) -/

open scoped RealInnerProductSpace

example : sampleMeanVec (E := ℝ) evens 2 = 1 := by
  norm_num [sampleMeanVec, evens, sum_range_succ]

example (ω : ℕ → ℕ → ℝ) : bootMeanVec (E := ℝ) 3 ω = bootMean 3 ω := by
  simp [bootMeanVec, bootMean]

theorem inner_real (z t : ℝ) : ⟪z, t⟫ = z * t := by simp [mul_comm]

theorem tendsto_sampleMean_alt_inner (t : ℝ) :
    Tendsto (fun n : ℕ => sampleMean (fun i => ⟪alt i, t⟫) (range n)) atTop (𝓝 0) := by
  have h := tendsto_sampleMean_alt.mul_const t
  rw [zero_mul] at h
  refine h.congr fun n => ?_
  simp only [inner_real, sampleMean_range, ← Finset.sum_mul, mul_assoc]

theorem tendsto_meanSq_alt_inner (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪alt i, t⟫ ^ 2) atTop (𝓝 (t ^ 2)) := by
  have h := tendsto_meanSq_alt.mul_const (t ^ 2)
  rw [one_mul] at h
  refine h.congr fun n => ?_
  simp only [inner_real, mul_pow, alt_sq, one_mul, mul_assoc, Finset.sum_mul]

/-- The bootstrap mean of the alternating data, viewed as data in the one-dimensional inner
product space `ℝ`, is conditionally asymptotically standard Gaussian, through the
Cramér–Wold route of `tendstoInDistribution_bootMeanVec`. -/
example : TendstoInDistribution
    (fun (n : ℕ) ω => √(n : ℝ) • (bootMeanVec n ω - sampleMeanVec alt n)) atTop (id : ℝ → ℝ)
    (fun _ => world alt) (gaussianReal 0 1) := by
  refine tendstoInDistribution_bootMeanVec alt measurable_id.aemeasurable
    (fun t => ‖t‖₊ ^ 2) (fun t => ⟨by fun_prop, ?_⟩)
    (fun t => ?_) (fun t => lindeberg_of_tendsto_sampleMean (tendsto_sampleMean_alt_inner t)
      (tendsto_meanSq_alt_inner t))
  · have hfun : (fun z : ℝ => ⟪id z, t⟫) = fun z => t * z := by
      funext z; simp
    rw [hfun, gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (by simp)
  · have h := tendsto_empiricalVar (tendsto_sampleMean_alt_inner t) (tendsto_meanSq_alt_inner t)
    simpa using h

/-! ### Non-vacuity: iid standard Gaussian data -/

/-- iid standard Gaussian coordinates. -/
noncomputable def gaussSeq : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure gaussSeq := by unfold gaussSeq; infer_instance

/-- Almost every iid standard Gaussian sample has a bootstrap mean that is conditionally
asymptotically `N(0, 1)`. -/
example : ∀ᵐ ω ∂gaussSeq, TendstoInDistribution
    (fun (n : ℕ) ω' => √(n : ℝ) * (bootMean n ω' - sampleMean (fun i => ω i) (range n))) atTop
    (id : ℝ → ℝ) (fun _ => world (fun i => ω i))
    (gaussianReal 0 1) := by
  have hmp : ∀ i, MeasurePreserving (fun ω : ℕ → ℝ => ω i) gaussSeq (gaussianReal 0 1) :=
    fun i => measurePreserving_eval_infinitePi _ i
  have hvar : variance (fun ω : ℕ → ℝ => ω 0) gaussSeq = 1 := by
    rw [← variance_id_map (hmp 0).measurable.aemeasurable, (hmp 0).map_eq,
      variance_id_gaussianReal]
    simp
  have hmem : MemLp (fun ω : ℕ → ℝ => ω 0) 2 gaussSeq :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving (hmp 0)
  have hind : Pairwise (Function.onFun (· ⟂ᵢ[gaussSeq] ·) fun (i : ℕ) (ω : ℕ → ℝ) => ω i) :=
    fun i j hij => (iIndepFun_infinitePi (P := fun _ => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id)).indepFun hij
  have hident : ∀ i, IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0) gaussSeq gaussSeq :=
    fun i => ⟨(hmp i).measurable.aemeasurable, (hmp 0).measurable.aemeasurable,
      by rw [(hmp i).map_eq, (hmp 0).map_eq]⟩
  have h := ae_tendstoInDistribution_bootMean (P := gaussSeq) (fun i ω => ω i) hmem hind hident
  rw [hvar, Real.toNNReal_one] at h
  exact h

/-! ### Non-vacuity in `ℝ²`, iid data with singular covariance -/

/-- The plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The rank-one map `z ↦ z₀ e₀`; images of a standard Gaussian have singular covariance. -/
noncomputable def rankOne : E2 →L[ℝ] E2 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1)

/-- iid standard Gaussian vectors in `ℝ²`. -/
noncomputable def gaussSeq2 : Measure (ℕ → E2) := Measure.infinitePi fun _ => stdGaussian E2

instance : IsProbabilityMeasure gaussSeq2 := by unfold gaussSeq2; infer_instance

/-- The data `X i = rankOne (G i)` for iid standard Gaussian `G i`. -/
noncomputable def rankOneData (i : ℕ) (ω : ℕ → E2) : E2 := rankOne (ω i)

/-- The covariance of the data is singular: the direction `e₁` carries no variance. -/
example (ω : ℕ → E2) : ⟪rankOneData 0 ω, EuclideanSpace.single 1 1⟫ = 0 := by
  simp [rankOneData, rankOne, EuclideanSpace.inner_single_right]

/-- The covariance is not zero either: the direction `e₀` carries variance `1`, so the data
covariance has rank exactly one. -/
example : Var[fun ω => ⟪rankOneData 0 ω, EuclideanSpace.single 0 1⟫; gaussSeq2] = 1 := by
  have hfun : (fun ω => ⟪rankOneData 0 ω, EuclideanSpace.single (0 : Fin 2) (1 : ℝ)⟫) =
      fun ω : ℕ → E2 => innerSL ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (ω 0) := by
    funext ω
    simp [rankOneData, rankOne, EuclideanSpace.inner_single_right,
      EuclideanSpace.inner_single_left]
  have hmp : MeasurePreserving (fun ω : ℕ → E2 => ω 0) gaussSeq2 (stdGaussian E2) :=
    measurePreserving_eval_infinitePi _ 0
  rw [hfun, hmp.variance_fun_comp (innerSL ℝ _).continuous.aemeasurable,
    variance_dual_stdGaussian, innerSL_apply_norm]
  simp

theorem rankOneData_hyps :
    MemLp (rankOneData 0) 2 gaussSeq2 ∧ iIndepFun rankOneData gaussSeq2 ∧
      ∀ i, IdentDistrib (rankOneData i) (rankOneData 0) gaussSeq2 gaussSeq2 := by
  have hmp : ∀ i, MeasurePreserving (fun ω : ℕ → E2 => ω i) gaussSeq2 (stdGaussian E2) :=
    fun i => measurePreserving_eval_infinitePi _ i
  refine ⟨rankOne.comp_memLp' (IsGaussian.memLp_two_id.comp_measurePreserving (hmp 0)),
    iIndepFun_infinitePi (P := fun _ => stdGaussian E2) (X := fun _ => rankOne)
      (fun _ => rankOne.continuous.measurable), fun i => ?_⟩
  have hid : IdentDistrib (fun ω : ℕ → E2 => ω i) (fun ω => ω 0) gaussSeq2 gaussSeq2 :=
    ⟨(hmp i).measurable.aemeasurable, (hmp 0).measurable.aemeasurable,
      by rw [(hmp i).map_eq, (hmp 0).map_eq]⟩
  exact hid.comp rankOne.continuous.measurable

/-- For iid data in `ℝ²` with singular covariance, the Gaussian limit `Z = A G` supplied by the
multivariate CLT is both the sampling limit and, almost surely, the conditional bootstrap
limit; this goes through the orthonormal-basis strong laws of the almost-sure vector theorem. -/
example : ∃ A : E2 →L[ℝ] E2,
    TendstoInDistribution
        (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ •
          (∑ k ∈ range n, rankOneData k ω - n • ∫ ω, rankOneData 0 ω ∂gaussSeq2))
        atTop (fun z => A z) (fun _ => gaussSeq2) (stdGaussian E2) ∧
      ∀ᵐ ω ∂gaussSeq2, TendstoInDistribution
        (fun (n : ℕ) ω' => √(n : ℝ) •
          (bootMeanVec n ω' - sampleMeanVec (fun i => rankOneData i ω) n))
        atTop (fun z => A z) (fun _ => world (fun i => rankOneData i ω)) (stdGaussian E2) := by
  obtain ⟨hmem, hind, hident⟩ := rankOneData_hyps
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal hmem
  exact ⟨A, bootstrap_consistent_mean rankOneData hmem hind hident
    A.continuous.measurable.aemeasurable hA⟩

/-- The almost-sure smooth vector theorem on the same data, with `g = id` (derivative `id`). -/
example : ∃ A : E2 →L[ℝ] E2, ∀ᵐ ω ∂gaussSeq2, TendstoInDistribution
    (fun (n : ℕ) ω' => √(n : ℝ) •
      (id (bootMeanVec n ω') - id (sampleMeanVec (fun i => rankOneData i ω) n)))
    atTop (fun z => ContinuousLinearMap.id ℝ E2 (A z))
    (fun _ => world (fun i => rankOneData i ω)) (stdGaussian E2) := by
  obtain ⟨hmem, hind, hident⟩ := rankOneData_hyps
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal hmem
  exact ⟨A, ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt rankOneData hmem
    (fun _ _ hij => hind.indepFun hij) hident A.continuous.measurable.aemeasurable hA
    (hasStrictFDerivAt_id _) measurable_id⟩

end MathlibExtTest.Probability.Statistics.Bootstrap
