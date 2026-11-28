/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CochranQ
public import Mathlib.Probability.Moments.Covariance

/-!
# DerSimonian–Laird estimators and random-effects pooling

When all sampling variances agree, the DerSimonian–Laird estimator is the sample variance
minus the common sampling variance, truncated at zero. The random-effects pooled estimate is the
arithmetic mean. With known variances and pairwise uncorrelated deviations, inverse-total-variance
weighting is unbiased and minimizes variance among weighted averages.

The declarations retain their original namespace for compatibility with the wanted module.
-/

@[expose] public section

namespace WantedExt.Probability.Statistics.DerSimonianLairdWanted

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MetaAnalysis

variable {k : ℕ}

/-- **Scaling of the moment estimator.** The scaling `S₁ - S₂ / S₁` with `S_r = ∑ w_i^r` for the
fixed-effect weights `w_i = v_i⁻¹`. -/
noncomputable def weightScale (v : Fin k → ℝ) : ℝ :=
  (∑ i, (v i)⁻¹) - (∑ i, ((v i)⁻¹) ^ 2) / ∑ i, (v i)⁻¹

/-- **Untruncated moment estimator.** The estimator `(Q - (k - 1)) / (S₁ - S₂ / S₁)` of `Δ²`, with
Cochran's `Q` for sampling variances `v`. -/
noncomputable def momentEstimator (v y : Fin k → ℝ) : ℝ :=
  (cochranQ v y - (k - 1)) / weightScale v

/-- **DerSimonian–Laird estimator.** The truncated moment estimator
`Δ̂² = max {0, (Q - (k - 1)) / (S₁ - S₂ / S₁)}`. -/
noncomputable def dlEstimator (v y : Fin k → ℝ) : ℝ :=
  max 0 (momentEstimator v y)

/-- **Random-effects pooled estimate.** The estimate `∑ᵢ ωᵢ yᵢ`, where `ω` are the inverse-variance
weights of the total variances `v_i + Δ²`. -/
noncomputable def pooledEstimate (v : Fin k → ℝ) (Δsq : ℝ) (y : Fin k → ℝ) : ℝ :=
  ∑ i, inverseVarianceWeights (fun j => v j + Δsq) i * y i

private theorem inverseVarianceWeights_const (hk : 0 < (k : ℝ)) {s : ℝ} (hs : 0 < s)
    (i : Fin k) : inverseVarianceWeights (fun _ : Fin k => s) i = 1 / k := by
  simp only [inverseVarianceWeights, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [hk.ne', hs.ne']

private theorem weightedMean_const (hk : 0 < (k : ℝ)) {s : ℝ} (hs : 0 < s) (y : Fin k → ℝ) :
    (∑ i, inverseVarianceWeights (fun _ : Fin k => s) i * y i) = (∑ i, y i) / k := by
  simp_rw [inverseVarianceWeights_const hk hs, ← Finset.mul_sum, one_div, div_eq_mul_inv]
  exact mul_comm _ _

private theorem weightScale_const (hk : 0 < (k : ℝ)) {s : ℝ} (hs : 0 < s) :
    weightScale (fun _ : Fin k => s) = ((k : ℝ) - 1) / s := by
  simp only [weightScale, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk.ne', hs.ne']

/-- **Equal sampling variances.** Let `k ≥ 2` and let every
sampling variance equal `s² > 0`. For real study estimates `y`, with `ȳ = ∑ y_i / k`: the
DerSimonian–Laird estimator is `max {0, ∑ (y_i - ȳ)² / (k - 1) - s²}`, and for every `Δ² ≥ 0`
the random-effects pooled estimate is `ȳ` with `(∑ᵢ (s² + Δ²)⁻¹)⁻¹ = (s² + Δ²) / k`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 183. -/
theorem equal_variances (hk : 2 ≤ k) (s2 : ℝ) (hs2 : 0 < s2) (y : Fin k → ℝ)
    (Δsq : ℝ) (hΔ : 0 ≤ Δsq) :
    dlEstimator (fun _ : Fin k => s2) y =
        max 0 ((∑ i, (y i - (∑ j, y j) / k) ^ 2) / (k - 1) - s2) ∧
      pooledEstimate (fun _ : Fin k => s2) Δsq y = (∑ j, y j) / k ∧
      (∑ _i : Fin k, (s2 + Δsq)⁻¹)⁻¹ = (s2 + Δsq) / k := by
  have hk₂ : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk₀ : 0 < (k : ℝ) := by linarith
  have hk₁ : 0 < (k : ℝ) - 1 := by linarith
  have htotal : 0 < s2 + Δsq := add_pos_of_pos_of_nonneg hs2 hΔ
  refine ⟨?_, weightedMean_const hk₀ htotal y, ?_⟩
  · rw [dlEstimator, momentEstimator, weightScale_const hk₀ hs2, cochranQ]
    simp_rw [weightedMean_const hk₀ hs2 y, ← Finset.mul_sum]
    congr 1
    generalize (∑ i : Fin k, (y i - (∑ j, y j) / k) ^ 2) = ss
    field_simp [hs2.ne', hk₁.ne']
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_rev, inv_inv, div_eq_mul_inv]

/-- **Random-effects model.** The assumptions on study effects `δ`, sampling errors `e`, known
sampling variances `v` and between-study variance `Δ²`: all `2k` deviations are square integrable
with mean `0`, `Var δ_i = Δ²`, `Var e_i = v_i`, and distinct deviations are uncorrelated. -/
structure RandomEffectsModel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (δ e : Fin k → Ω → ℝ) (v : Fin k → ℝ) (Δsq : ℝ) : Prop where
  memLp_δ : ∀ i, MemLp (δ i) 2 μ
  memLp_e : ∀ i, MemLp (e i) 2 μ
  mean_δ : ∀ i, ∫ ω, δ i ω ∂μ = 0
  mean_e : ∀ i, ∫ ω, e i ω ∂μ = 0
  var_δ : ∀ i, Var[δ i; μ] = Δsq
  var_e : ∀ i, Var[e i; μ] = v i
  cov_δδ : ∀ i j, i ≠ j → cov[δ i, δ j; μ] = 0
  cov_ee : ∀ i j, i ≠ j → cov[e i, e j; μ] = 0
  cov_δe : ∀ i j, cov[δ i, e j; μ] = 0

/-- **The random-effects pooled estimate with known `Δ²`.**
Under the hypotheses of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, sampling variances
`v_i > 0`, `Δ² ≥ 0`, `y_i = m + δ_i + e_i` with the random-effects model assumptions), the pooled
estimate `∑ᵢ ωᵢ yᵢ` with the inverse-variance weights `ω` of `v_i + Δ²` has expectation `m` and
variance `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`, and every weighted average `∑ c_i y_i` with `∑ c_i = 1` has
variance at least `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 183, equations (2)–(4). -/
theorem pooledEstimate_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e v Δsq)
    (c : Fin k → ℝ) (hc : ∑ i, c i = 1) :
    ∫ ω, pooledEstimate v Δsq (fun i => m + δ i ω + e i ω) ∂μ = m ∧
      Var[fun ω => pooledEstimate v Δsq (fun i => m + δ i ω + e i ω); μ] =
        (∑ i, (v i + Δsq)⁻¹)⁻¹ ∧
      (∑ i, (v i + Δsq)⁻¹)⁻¹ ≤ Var[fun ω => ∑ i, c i * (m + δ i ω + e i ω); μ] := by
  let X : Fin k → Ω → ℝ := fun i ω => m + δ i ω + e i ω
  let s : Fin k → ℝ := fun i => v i + Δsq
  have hs : ∀ i, 0 < s i := fun i => add_pos_of_pos_of_nonneg (hv i) hΔ
  have hk₀ : 0 < k := by omega
  have hX : ∀ i, MemLp (X i) 2 μ := fun i =>
    ((memLp_const m).add (hmodel.memLp_δ i)).add (hmodel.memLp_e i)
  have hmean (i : Fin k) : ∫ ω, X i ω ∂μ = m := by
    have hδ := (hmodel.memLp_δ i).integrable one_le_two
    have he := (hmodel.memLp_e i).integrable one_le_two
    calc
      (∫ ω, X i ω ∂μ) = (∫ ω, m + δ i ω ∂μ) + ∫ ω, e i ω ∂μ :=
        integral_add ((integrable_const m).add hδ) he
      _ = m := by
        rw [integral_add (integrable_const m) hδ]
        simp [hmodel.mean_δ, hmodel.mean_e]
  -- The mixed effect/error terms vanish even within the same study.
  have hXeq (i : Fin k) : X i = fun ω => m + (δ i + e i) ω := by
    funext ω
    exact add_assoc _ _ _
  have hdev (i : Fin k) : MemLp (δ i + e i) 2 μ :=
    (hmodel.memLp_δ i).add (hmodel.memLp_e i)
  have hcov (i j : Fin k) : cov[X i, X j; μ] = cov[δ i, δ j; μ] + cov[e i, e j; μ] := by
    simp only [hXeq]
    rw [covariance_const_add_left ((hdev i).integrable one_le_two),
      covariance_const_add_right ((hdev j).integrable one_le_two)]
    rw [covariance_add_left (hmodel.memLp_δ i) (hmodel.memLp_e i) (hdev j),
      covariance_add_right (hmodel.memLp_δ i) (hmodel.memLp_δ j) (hmodel.memLp_e j),
      covariance_add_right (hmodel.memLp_e i) (hmodel.memLp_δ j) (hmodel.memLp_e j),
      covariance_comm (e i) (δ j), hmodel.cov_δe i j, hmodel.cov_δe j i, add_zero, zero_add]
  have hdiag (i : Fin k) : cov[X i, X i; μ] = s i := by
    rw [hcov, covariance_self (hmodel.memLp_δ i).aemeasurable,
      covariance_self (hmodel.memLp_e i).aemeasurable, hmodel.var_δ, hmodel.var_e, add_comm]
  have hoff (i j : Fin k) (hij : i ≠ j) : cov[X i, X j; μ] = 0 := by
    rw [hcov, hmodel.cov_δδ i j hij, hmodel.cov_ee i j hij, add_zero]
  have hweighted (a : Fin k → ℝ) (i : Fin k) : MemLp (fun ω => a i * X i ω) 2 μ :=
    (hX i).const_mul (a i)
  have hvar (a : Fin k → ℝ) :
      Var[fun ω => ∑ i, a i * X i ω; μ] = ∑ i, a i ^ 2 * s i := by
    have hsum := memLp_finsetSum Finset.univ (fun i _ => hweighted a i)
    rw [← covariance_self hsum.aemeasurable, covariance_fun_sum_fun_sum (hweighted a) (hweighted a)]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i), hdiag]
    · simp only [pow_two, mul_assoc]
    · intro j _ hji
      rw [hoff i j hji.symm, mul_zero, mul_zero]
  unfold pooledEstimate
  change (∫ ω, ∑ i, inverseVarianceWeights s i * X i ω ∂μ) = m ∧
    Var[fun ω => ∑ i, inverseVarianceWeights s i * X i ω; μ] = (∑ i, (s i)⁻¹)⁻¹ ∧
    (∑ i, (s i)⁻¹)⁻¹ ≤ Var[fun ω => ∑ i, c i * X i ω; μ]
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ => (hweighted (inverseVarianceWeights s) i).integrable
      one_le_two]
    simp_rw [integral_const_mul, hmean]
    rw [← Finset.sum_mul, sum_inverseVarianceWeights hs hk₀, one_mul]
  · rw [hvar, sum_sq_mul_inverseVarianceWeights hs hk₀]
  · rw [hvar]
    exact inv_sum_inv_le_sum_sq_mul hs hc

end WantedExt.Probability.Statistics.DerSimonianLairdWanted
