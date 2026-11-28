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

For `k ≥ 2` studies with known sampling variances `v_i > 0` and between-study variance `Δ² ≥ 0`,
let `y_i = m + δ_i + e_i` on a probability space. The deviations are square integrable and
centered, with variances `Δ²` for `δ_i` and `v_i` for `e_i`, and distinct deviations are
uncorrelated. The expected fixed-effect Cochran `Q` is `k - 1 + Δ² (S₁ - S₂ / S₁)`, where
`S_r = ∑ᵢ (v_i⁻¹)^r`, and `S₁ - S₂ / S₁` is positive. Only the means and covariances are
needed, not Gaussianity or independence.

When all sampling variances agree, the DerSimonian–Laird estimator is the sample variance
minus the common sampling variance, truncated at zero. The random-effects pooled estimate is the
arithmetic mean. In the same random-effects model, inverse-total-variance weighting is unbiased
and minimizes variance among weighted averages with weights summing to one.

The declarations retain their original namespace for compatibility with the wanted module.

## References

* Rebecca DerSimonian and Nan Laird, *Meta-Analysis in Clinical Trials*, Controlled Clinical Trials
  7 (1986), 177–188, pp. 180–183: the random-effects model, the moment calculation in
  “Estimation and Computation” (pp. 182–183), and equations (2)–(4) for pooling.
* The covariance calculation is shared with `pooledEstimate_optimal` in
  `MathlibExt.Probability.Statistics.DerSimonianLaird`.
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

/-- **Pairwise form of the moment scale.** Each inverse-variance weight is multiplied by the
sum of the other inverse-variance weights; the sum of these products is divided by the total
inverse-variance weight. -/
theorem weightScale_eq_sum_mul_sub (v : Fin k → ℝ) :
    weightScale v = (∑ i, (v i)⁻¹ * ((∑ j, (v j)⁻¹) - (v i)⁻¹)) / ∑ j, (v j)⁻¹ := by
  let S := ∑ i, (v i)⁻¹
  change S - (∑ i, ((v i)⁻¹) ^ 2) / S = (∑ i, (v i)⁻¹ * (S - (v i)⁻¹)) / S
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← pow_two]
  change S - (∑ i, ((v i)⁻¹) ^ 2) / S = (S * S - (∑ i, ((v i)⁻¹) ^ 2)) / S
  by_cases hS : S = 0
  · simp [hS]
  · field_simp

private theorem weightedMean_const (hk : 0 < (k : ℝ)) {s : ℝ} (hs : 0 < s) (y : Fin k → ℝ) :
    (∑ i, inverseVarianceWeights (fun _ : Fin k => s) i * y i) = (∑ i, y i) / k := by
  rw [sum_inverseVarianceWeights_mul]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk.ne', hs.ne']

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
  · have hcenter : (∑ i, s2⁻¹ * (y i - (∑ j, y j) / k)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hk₀.ne']
      ring
    rw [dlEstimator, momentEstimator, weightScale_const hk₀ hs2,
      cochranQ_eq_sum_sq_sub (fun _ => hs2) ((∑ j, y j) / k), hcenter]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, sub_zero, ← Finset.mul_sum]
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

private theorem RandomEffectsModel.covariance_studyEstimates {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {δ e : Fin k → Ω → ℝ} {v : Fin k → ℝ} {Δsq : ℝ}
    (hmodel : RandomEffectsModel μ δ e v Δsq) (m : ℝ) (i j : Fin k) :
    cov[fun ω => m + δ i ω + e i ω, fun ω => m + δ j ω + e j ω; μ] =
      if i = j then v i + Δsq else 0 := by
  have hdev (l : Fin k) : MemLp (δ l + e l) 2 μ :=
    (hmodel.memLp_δ l).add (hmodel.memLp_e l)
  have hshift (l : Fin k) : (fun ω => m + δ l ω + e l ω) = fun ω => m + (δ l + e l) ω := by
    funext ω
    exact add_assoc _ _ _
  rw [hshift i, hshift j, covariance_const_add_left ((hdev i).integrable one_le_two),
    covariance_const_add_right ((hdev j).integrable one_le_two)]
  rw [covariance_add_left (hmodel.memLp_δ i) (hmodel.memLp_e i) (hdev j),
    covariance_add_right (hmodel.memLp_δ i) (hmodel.memLp_δ j) (hmodel.memLp_e j),
    covariance_add_right (hmodel.memLp_e i) (hmodel.memLp_δ j) (hmodel.memLp_e j),
    covariance_comm (e i) (δ j), hmodel.cov_δe i j, hmodel.cov_δe j i, add_zero, zero_add]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (rfl : i = i), covariance_self (hmodel.memLp_δ i).aemeasurable,
      covariance_self (hmodel.memLp_e i).aemeasurable, hmodel.var_δ, hmodel.var_e, add_comm]
  · rw [ite_eq_right hij, hmodel.cov_δδ i j hij, hmodel.cov_ee i j hij, add_zero]

private theorem RandomEffectsModel.variance_weighted_studyEstimates {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {δ e : Fin k → Ω → ℝ}
    {v : Fin k → ℝ} {Δsq : ℝ} (hmodel : RandomEffectsModel μ δ e v Δsq)
    (m : ℝ) (a : Fin k → ℝ) :
    Var[fun ω => ∑ i, a i * (m + δ i ω + e i ω); μ] = ∑ i, a i ^ 2 * (v i + Δsq) := by
  have hweighted (i : Fin k) : MemLp (fun ω => a i * (m + δ i ω + e i ω)) 2 μ :=
    (((memLp_const m).add (hmodel.memLp_δ i)).add (hmodel.memLp_e i)).const_mul (a i)
  rw [variance_fun_sum hweighted]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hmodel.covariance_studyEstimates]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [pow_two, mul_assoc]
  · intro j _ hji
    rw [ite_eq_right hji.symm, mul_zero, mul_zero]

/-- **Expectation of Cochran's `Q`.** Let `μ` be a
probability measure, `k ≥ 2`, `v_i > 0` known sampling variances, `Δ² ≥ 0`, and
`y_i = m + δ_i + e_i` where `δ, e` satisfy the random-effects model assumptions (square
integrable, mean `0`, `Var δ_i = Δ²`, `Var e_i = v_i`, distinct deviations uncorrelated). Then
`S₁ - S₂ / S₁ > 0` and `E[cochranQ v y] = (k - 1) + Δ² (S₁ - S₂ / S₁)`, with `S_r = ∑ (v_i⁻¹)^r`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 182 (the moment equation). -/
theorem integral_cochranQ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e v Δsq) :
    0 < weightScale v ∧
      ∫ ω, cochranQ v (fun i => m + δ i ω + e i ω) ∂μ = (k - 1) + Δsq * weightScale v := by
  have _ := hΔ  -- Nonnegativity also follows from the model's variance identity.
  let w : Fin k → ℝ := fun i => (v i)⁻¹
  let S := ∑ i, w i
  have hnonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hw (i : Fin k) : 0 < w i := inv_pos.mpr (hv i)
  have hS : 0 < S := Finset.sum_pos (fun i _ => hw i) hnonempty
  constructor
  · rw [weightScale_eq_sum_mul_sub]
    change 0 < (∑ i, w i * (S - w i)) / S
    refine div_pos (Finset.sum_pos (fun i _ => mul_pos (hw i) ?_) hnonempty) hS
    have herase : (Finset.univ.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hsplit := Finset.sum_erase_add Finset.univ w (Finset.mem_univ i)
    change 0 < (∑ j, w j) - w i
    rw [← hsplit, add_sub_cancel_right]
    exact Finset.sum_pos (fun j _ => hw j) herase
  let Z (i : Fin k) (ω : Ω) := δ i ω + e i ω
  let T (ω : Ω) := ∑ i, w i * Z i ω
  have hZ (i : Fin k) : MemLp (Z i) 2 μ := (hmodel.memLp_δ i).add (hmodel.memLp_e i)
  have hweighted (i : Fin k) : MemLp (fun ω => w i * Z i ω) 2 μ := (hZ i).const_mul (w i)
  have hT : MemLp T 2 μ := memLp_finsetSum Finset.univ (fun i _ => hweighted i)
  have hZmean (i : Fin k) : (∫ ω, Z i ω ∂μ) = 0 := by
    dsimp only [Z]
    rw [integral_add ((hmodel.memLp_δ i).integrable one_le_two)
      ((hmodel.memLp_e i).integrable one_le_two), hmodel.mean_δ, hmodel.mean_e, add_zero]
  have hTmean : (∫ ω, T ω ∂μ) = 0 := by
    dsimp only [T]
    rw [integral_finsetSum _ fun i _ => (hweighted i).integrable one_le_two]
    simp [integral_const_mul, hZmean]
  have hZsq (i : Fin k) : (∫ ω, Z i ω ^ 2 ∂μ) = v i + Δsq := by
    have hvar : Var[Z i; μ] = v i + Δsq := by
      rw [← covariance_self (hZ i).aemeasurable]
      simpa [Z] using hmodel.covariance_studyEstimates 0 i i
    simpa only [variance_eq_integral (hZ i).aemeasurable, hZmean, sub_zero] using hvar
  have hTsq : (∫ ω, T ω ^ 2 ∂μ) = ∑ i, w i ^ 2 * (v i + Δsq) := by
    have hvar : Var[T; μ] = ∑ i, w i ^ 2 * (v i + Δsq) := by
      simpa only [T, Z, zero_add] using hmodel.variance_weighted_studyEstimates 0 w
    simpa only [variance_eq_integral hT.aemeasurable, hTmean, sub_zero] using hvar
  have hQ (ω : Ω) : cochranQ v (fun i => m + δ i ω + e i ω) =
      (∑ i, w i * Z i ω ^ 2) - T ω ^ 2 / S := by
    simpa [w, S, T, Z, add_assoc] using
      cochranQ_eq_sum_sq_sub hv m (fun i => m + δ i ω + e i ω)
  have hsumInt (i : Fin k) : Integrable (fun ω => w i * Z i ω ^ 2) μ :=
    (hZ i).integrable_sq.const_mul (w i)
  simp_rw [hQ]
  rw [integral_sub (integrable_finsetSum _ fun i _ => hsumInt i) (hT.integrable_sq.div_const S),
    integral_finsetSum _ (fun i _ => hsumInt i), integral_div, hTsq]
  simp_rw [integral_const_mul, hZsq]
  have hwv (i : Fin k) : w i * v i = 1 := inv_mul_cancel₀ (hv i).ne'
  have hlinear : (∑ i, w i * (v i + Δsq)) = (k : ℝ) + S * Δsq := by
    simp only [mul_add, Finset.sum_add_distrib, hwv, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, S]
  have hquad : (∑ i, w i ^ 2 * (v i + Δsq)) = S + (∑ i, w i ^ 2) * Δsq := by
    have h (i : Fin k) : w i ^ 2 * v i = w i := by rw [pow_two, mul_assoc, hwv, mul_one]
    simp only [mul_add, Finset.sum_add_distrib, h, ← Finset.sum_mul, S]
  rw [hlinear, hquad, weightScale, add_div, div_self hS.ne']
  change (k : ℝ) + S * Δsq - (1 + (∑ i, w i ^ 2) * Δsq / S) =
    (k : ℝ) - 1 + Δsq * (S - (∑ i, w i ^ 2) / S)
  ring

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
  have hweighted (a : Fin k → ℝ) (i : Fin k) : MemLp (fun ω => a i * X i ω) 2 μ :=
    (hX i).const_mul (a i)
  have hvar (a : Fin k → ℝ) :
      Var[fun ω => ∑ i, a i * X i ω; μ] = ∑ i, a i ^ 2 * s i :=
    hmodel.variance_weighted_studyEstimates m a
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
