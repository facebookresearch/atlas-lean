/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Meta-analysis: combining p-values and estimates

Combination rules for `k` independent studies of the same hypothesis or parameter.

* `fisherStatistic p = -2 ∑ log pᵢ`: Fisher's combined statistic of `k` p-values.
* `stoufferStatistic w z = ∑ wᵢ zᵢ / ‖w‖`: Stouffer's weighted z statistic of the study
  z-scores `zᵢ` (for one-sided p-values `zᵢ = Φ⁻¹(1 - pᵢ)`; that transform is not formalized
  here, so the statement starts from the z-scores).
* `inverseVarianceWeights v i = vᵢ⁻¹ / ∑ⱼ vⱼ⁻¹`: the fixed-effect (inverse-variance) weights.

## Main results

* `hasLaw_neg_two_mul_log_uniform`: `-2 log U ~ χ²₂` for `U` uniform on `[0, 1]`.
  (MGF uniqueness for gamma laws, `ProbabilityTheory.eq_gammaMeasure_of_mgf_eq`, and the
  gamma exponential-moment set, `ProbabilityTheory.integrableExpSet_gammaMeasure`, live in
  `Distributions.Gamma`.)
* `hasLaw_fisherStatistic`: for `k ≥ 1` independent p-values uniform on `[0, 1]`,
  `-2 ∑ log pᵢ ~ χ²_{2k}` (Fisher 1932, §21.1).
* `hasLaw_stoufferStatistic`: for independent standard normal z-scores and weights `w ≠ 0`,
  `∑ wᵢ zᵢ / ‖w‖ ~ N(0, 1)` (Stouffer et al. 1949; Liptak 1958).
* `inv_sum_inv_le_sum_sq_mul`: among weights summing to one, `∑ cᵢ² vᵢ ≥ (∑ vᵢ⁻¹)⁻¹`, with
  equality at the inverse-variance weights (`sum_sq_mul_inverseVarianceWeights`).
* `variance_inverseVariance_le`: for pairwise independent square-integrable estimates with
  positive variances, the inverse-variance-weighted average has the smallest variance among all
  weighted averages with weights summing to one (Cochran 1954).

Cochran's `Q ~ χ²_{k-1}` is `hasLaw_cochranQ` in
`MathlibExt/Probability/Statistics/CochranQ.lean`.

## References

* R. A. Fisher, *Statistical Methods for Research Workers*, 4th ed., Oliver and Boyd (1932),
  §21.1.
* S. A. Stouffer, E. A. Suchman, L. C. DeVinney, S. A. Star and R. M. Williams, *The American
  Soldier*, vol. 1, Princeton University Press (1949).
* T. Liptak, *On the combination of independent tests*, Magyar Tud. Akad. Mat. Kutató Int.
  Közl. 3 (1958), 171–197.
* W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10
  (1954), 101–129.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MetaAnalysis

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-! ### Fisher's method -/

/-- Fisher's combined statistic `-2 ∑ log pᵢ` of `k` p-values. -/
noncomputable def fisherStatistic (p : Fin k → ℝ) : ℝ := -2 * ∑ i, Real.log (p i)

/-- `-2 log U` has the exponential law of rate `1/2`, i.e. chi-square with two degrees of
freedom, when `U` is uniform on `[0, 1]`. -/
theorem hasLaw_neg_two_mul_log_uniform :
    HasLaw (fun u : ℝ => -2 * Real.log u) (gammaMeasure 1 (1 / 2))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hf : Measurable fun u : ℝ => -2 * Real.log u := Real.measurable_log.const_mul _
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have := isProbabilityMeasure_gammaMeasure (a := 1) (r := 1 / 2) one_pos (by norm_num)
  refine ⟨hf.aemeasurable, ?_⟩
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hf measurableSet_Iic, Measure.restrict_apply (hf measurableSet_Iic),
    ← ofReal_cdf, show gammaMeasure 1 (1 / 2) = expMeasure (1 / 2) from rfl,
    cdf_expMeasure_eq (by norm_num)]
  split_ifs with hx
  · set e := Real.exp (-(1 / 2 * x))
    have he0 : 0 < e := Real.exp_pos _
    have hsub1 : Icc e 1 ⊆ (fun u : ℝ => -2 * Real.log u) ⁻¹' Iic x ∩ Icc 0 1 := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le he0 hu.1
      refine ⟨?_, hu0.le, hu.2⟩
      have : Real.log e ≤ Real.log u := Real.log_le_log he0 hu.1
      rw [Real.log_exp] at this
      simp only [mem_preimage, mem_Iic]
      linarith
    have hsub2 : (fun u : ℝ => -2 * Real.log u) ⁻¹' Iic x ∩ Icc 0 1 ⊆ insert 0 (Icc e 1) := by
      rintro u ⟨hu, hu0, hu1⟩
      rcases hu0.eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      refine Or.inr ⟨?_, hu1⟩
      simp only [mem_preimage, mem_Iic] at hu
      have : -(1 / 2 * x) ≤ Real.log u := by linarith
      exact (Real.le_log_iff_exp_le h0).1 this
    have hvol : volume (Icc e 1) = ENNReal.ofReal (1 - e) := Real.volume_Icc
    refine le_antisymm ?_ ?_
    · calc volume ((fun u : ℝ => -2 * Real.log u) ⁻¹' Iic x ∩ Icc 0 1)
          ≤ volume (insert 0 (Icc e 1)) := measure_mono hsub2
        _ ≤ volume ({0} : Set ℝ) + volume (Icc e 1) := by
            rw [insert_eq]; exact measure_union_le _ _
        _ = ENNReal.ofReal (1 - e) := by rw [Real.volume_singleton, zero_add, hvol]
    · rw [← hvol]; exact measure_mono hsub1
  · have hempty : (fun u : ℝ => -2 * Real.log u) ⁻¹' Iic x ∩ Icc 0 1 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro u ⟨hu, hu0, hu1⟩
      simp only [mem_preimage, mem_Iic] at hu
      have := Real.log_nonpos hu0 hu1
      linarith
    rw [hempty]
    simp

/-- Fisher (1932), §21.1: for `k ≥ 1` independent p-values, each uniform on `[0, 1]`, Fisher's
statistic `-2 ∑ log pᵢ` is chi-square with `2k` degrees of freedom. -/
theorem hasLaw_fisherStatistic (hk : 0 < k) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : Fin k → Ω → ℝ} (hlaw : ∀ i, HasLaw (p i) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hind : iIndepFun p μ) :
    HasLaw (fun ω => fisherStatistic fun i => p i ω) (chiSquareMeasure (2 * k)) μ := by
  set Y : Fin k → Ω → ℝ := fun i ω => -2 * Real.log (p i ω) with hY
  have hYlaw : ∀ i, HasLaw (Y i) (gammaMeasure 1 (1 / 2)) μ :=
    fun i => hasLaw_neg_two_mul_log_uniform.comp (hlaw i)
  have hYind : iIndepFun Y μ :=
    hind.comp (fun _ x => -2 * Real.log x) fun _ => Real.measurable_log.const_mul _
  have hYmeas : ∀ i, AEMeasurable (Y i) μ := fun i => (hYlaw i).aemeasurable
  have hstat : (fun ω => fisherStatistic fun i => p i ω) = ∑ i, Y i := by
    funext ω
    simp [fisherStatistic, hY, Finset.mul_sum]
  have hchi : chiSquareMeasure (2 * k) = gammaMeasure (k : ℝ) (1 / 2) := by
    rw [chiSquareMeasure]
    congr 1
    push_cast
    ring
  rw [hstat, hchi]
  have hsm : AEMeasurable (∑ i, Y i) μ := Finset.aemeasurable_sum _ fun i _ => hYmeas i
  have := isProbabilityMeasure_gammaMeasure (a := 1) (r := 1 / 2) one_pos (by norm_num)
  refine ⟨hsm, ProbabilityTheory.eq_gammaMeasure_of_mgf_eq (by exact_mod_cast hk) (by norm_num) ?_⟩
  funext t
  rw [mgf_id_map hsm, hYind.mgf_sum₀ hYmeas]
  have h1 : ∀ i, mgf (Y i) μ t = mgf id (gammaMeasure 1 (1 / 2)) t := by
    intro i
    rw [← mgf_id_map (hYmeas i), (hYlaw i).map_eq]
  simp_rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases ht : t < 1 / 2
  · rw [mgf_gammaMeasure_of_lt one_pos (by norm_num) ht,
      mgf_gammaMeasure_of_lt (by exact_mod_cast hk) (by norm_num) ht, Real.rpow_one,
      Real.rpow_natCast]
  · have h0 : ∀ a : ℝ, 0 < a → mgf id (gammaMeasure a (1 / 2)) t = 0 := by
      intro a ha
      exact integral_undef (ProbabilityTheory.not_integrable_exp_mul_gammaMeasure ha (by norm_num)
        (not_lt.1 ht))
    rw [h0 1 one_pos, h0 k (by exact_mod_cast hk), zero_pow hk.ne']

/-! ### Stouffer's method -/

private theorem variance_sum_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (c : Fin k → ℝ) :
    Var[fun ω => ∑ i, c i * X i ω; μ] = ∑ i, c i ^ 2 * Var[X i; μ] := by
  have h := IndepFun.variance_sum (μ := μ) (X := fun i ω => c i * X i ω) (s := Finset.univ)
    (fun i _ => (hX i).const_mul (c i))
    (fun i _ j _ hij =>
      (hind hij).comp (measurable_const_mul (c i)) (measurable_const_mul (c j)))
  have he : (∑ i, fun ω => c i * X i ω) = fun ω => ∑ i, c i * X i ω := by
    ext ω; simp [Finset.sum_apply]
  rw [he] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => variance_const_mul (c i) (X i) μ

/-- Stouffer's weighted z statistic `∑ wᵢ zᵢ / √(∑ wᵢ²)` of the study z-scores `zᵢ`. -/
noncomputable def stoufferStatistic (w z : Fin k → ℝ) : ℝ :=
  (∑ i, w i * z i) / √(∑ i, w i ^ 2)

/-- Stouffer's method (Stouffer et al. 1949; Liptak 1958): for independent standard normal
z-scores and a nonzero weight vector, the weighted z statistic is standard normal. -/
theorem hasLaw_stoufferStatistic {μ : Measure Ω} [IsProbabilityMeasure μ] {w : Fin k → ℝ}
    (hw : w ≠ 0) {z : Fin k → Ω → ℝ} (hlaw : ∀ i, HasLaw (z i) (gaussianReal 0 1) μ)
    (hind : iIndepFun z μ) :
    HasLaw (fun ω => stoufferStatistic w fun i => z i ω) (gaussianReal 0 1) μ := by
  have hpos : 0 < ∑ i, w i ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
    exact lt_of_lt_of_le (pow_pos (abs_pos.2 hj) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (fun i _ => sq_nonneg (w i)) (Finset.mem_univ j))
  have hn0 : 0 < √(∑ i, w i ^ 2) := Real.sqrt_pos.2 hpos
  set c : Fin k → ℝ := fun i => w i / √(∑ i, w i ^ 2) with hc
  have hstat : (fun ω => stoufferStatistic w fun i => z i ω) = fun ω => ∑ i, c i * z i ω := by
    funext ω
    simp only [stoufferStatistic, hc, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hc2 : ∑ i, c i ^ 2 = 1 := by
    simp only [hc, div_pow, ← Finset.sum_div, Real.sq_sqrt hpos.le]
    exact div_self hpos.ne'
  have hL2 : ∀ i, MemLp (z i) 2 μ := fun i => (hlaw i).memLp (memLp_id_gaussianReal 2)
  have hY : ∀ i, HasGaussianLaw (fun ω => c i * z i ω) μ :=
    fun i => (gaussianReal_const_mul (hlaw i) (c i)).hasGaussianLaw
  have hindY : iIndepFun (fun i ω => c i * z i ω) μ :=
    hind.comp (fun i x => c i * x) fun i => measurable_const_mul _
  have hG := hindY.hasGaussianLaw_fun_sum hY
  rw [hstat]
  refine ⟨Finset.aemeasurable_fun_sum _ fun i _ => ((hlaw i).aemeasurable.const_mul (c i)), ?_⟩
  rw [hG.map_eq_gaussianReal, variance_sum_mul hL2 (fun i j hij => hind.indepFun hij)]
  congr 1
  · rw [integral_finsetSum _ fun i _ => ((hL2 i).integrable one_le_two).const_mul (c i)]
    simp [integral_const_mul, (hlaw _).integral_eq, integral_id_gaussianReal]
  · simp [(hlaw _).variance_eq, variance_id_gaussianReal, hc2]

/-! ### Inverse-variance weighting -/

/-- The inverse-variance (fixed-effect) weights `vᵢ⁻¹ / ∑ⱼ vⱼ⁻¹` for study variances `v`. -/
noncomputable def inverseVarianceWeights (v : Fin k → ℝ) (i : Fin k) : ℝ :=
  (v i)⁻¹ / ∑ j, (v j)⁻¹

private theorem sum_inv_pos {v : Fin k → ℝ} (hv : ∀ i, 0 < v i) (hk : 0 < k) :
    0 < ∑ j, (v j)⁻¹ :=
  Finset.sum_pos (fun i _ => inv_pos.2 (hv i)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-- The inverse-variance weights sum to one. -/
theorem sum_inverseVarianceWeights {v : Fin k → ℝ} (hv : ∀ i, 0 < v i) (hk : 0 < k) :
    ∑ i, inverseVarianceWeights v i = 1 := by
  simp only [inverseVarianceWeights, ← Finset.sum_div]
  exact div_self (sum_inv_pos hv hk).ne'

/-- The variance `∑ wᵢ² vᵢ` of the inverse-variance-weighted average is `(∑ vᵢ⁻¹)⁻¹`. -/
theorem sum_sq_mul_inverseVarianceWeights {v : Fin k → ℝ} (hv : ∀ i, 0 < v i) (hk : 0 < k) :
    ∑ i, inverseVarianceWeights v i ^ 2 * v i = (∑ j, (v j)⁻¹)⁻¹ := by
  have hS := (sum_inv_pos hv hk).ne'
  have h : ∀ i, inverseVarianceWeights v i ^ 2 * v i =
      (v i)⁻¹ / (∑ j, (v j)⁻¹) ^ 2 := by
    intro i
    have := (hv i).ne'
    simp only [inverseVarianceWeights]
    field_simp
  simp_rw [h, ← Finset.sum_div]
  field_simp

/-- Optimality of inverse-variance weighting: for positive variances `v` and weights `c` summing
to one, `∑ cᵢ² vᵢ ≥ (∑ vᵢ⁻¹)⁻¹`. The gap is `∑ vᵢ (cᵢ - wᵢ)²` for the inverse-variance
weights `w`. -/
theorem inv_sum_inv_le_sum_sq_mul {v : Fin k → ℝ} (hv : ∀ i, 0 < v i) {c : Fin k → ℝ}
    (hc : ∑ i, c i = 1) :
    (∑ j, (v j)⁻¹)⁻¹ ≤ ∑ i, c i ^ 2 * v i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hc
  have hS : 0 < ∑ j, (v j)⁻¹ := sum_inv_pos hv hk
  set w := inverseVarianceWeights v with hw
  have hvw : ∀ i, v i * w i = (∑ j, (v j)⁻¹)⁻¹ := by
    intro i
    have := (hv i).ne'
    rw [hw, inverseVarianceWeights]
    field_simp
  have hgap : ∑ i, c i ^ 2 * v i - (∑ j, (v j)⁻¹)⁻¹ = ∑ i, v i * (c i - w i) ^ 2 := by
    have e : ∀ i, v i * (c i - w i) ^ 2 =
        c i ^ 2 * v i - 2 * c i * (∑ j, (v j)⁻¹)⁻¹ + w i * (∑ j, (v j)⁻¹)⁻¹ := by
      intro i
      rw [← hvw i]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hc, hw,
      sum_inverseVarianceWeights hv hk]
    ring
  have hnn : 0 ≤ ∑ i, v i * (c i - w i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i).le (sq_nonneg _)
  linarith

/-- Cochran (1954): for pairwise independent square-integrable estimates `X i` with positive
variances, the inverse-variance-weighted average has variance `(∑ Var[Xᵢ]⁻¹)⁻¹`, the smallest
variance among all weighted averages `∑ cᵢ Xᵢ` with `∑ cᵢ = 1`. -/
theorem variance_inverseVariance_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hv : ∀ i, 0 < Var[X i; μ])
    {c : Fin k → ℝ} (hc : ∑ i, c i = 1) :
    Var[fun ω => ∑ i, inverseVarianceWeights (fun j => Var[X j; μ]) i * X i ω; μ] =
        (∑ j, (Var[X j; μ])⁻¹)⁻¹ ∧
      (∑ j, (Var[X j; μ])⁻¹)⁻¹ ≤ Var[fun ω => ∑ i, c i * X i ω; μ] := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hc
  rw [variance_sum_mul hX hind, variance_sum_mul hX hind]
  exact ⟨sum_sq_mul_inverseVarianceWeights hv hk, inv_sum_inv_le_sum_sq_mul hv hc⟩

end MathlibExt.Probability.Statistics.MetaAnalysis
