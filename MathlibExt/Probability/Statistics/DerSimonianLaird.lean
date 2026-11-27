/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CochranQ

/-!
# DerSimonian–Laird estimators for equal sampling variances

When all sampling variances agree, the DerSimonian–Laird estimator is the sample variance
minus the common sampling variance, truncated at zero. The random-effects pooled estimate is the
arithmetic mean.

The declarations retain their original namespace for compatibility with the wanted module.
-/

@[expose] public section

namespace WantedExt.Probability.Statistics.DerSimonianLairdWanted

open MathlibExt.Probability.Statistics.MetaAnalysis

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

end WantedExt.Probability.Statistics.DerSimonianLairdWanted
