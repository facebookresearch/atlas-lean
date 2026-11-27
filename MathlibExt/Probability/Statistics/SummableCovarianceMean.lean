/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Consistency of the sample mean under summable autocovariances

For a second-order stationary real sequence with mean `m` and absolutely summable
autocovariances, the variance of the sample mean is at most
`(γ 0 + 2 ∑_{h ≥ 1} |γ h|) / L`. Hence the sample mean tends to `m` in mean square and in
probability. In fixed finite dimension the same holds coordinatewise.

This is a weak law only: no central limit theorem and no mixing hypothesis are claimed.

## References

* P. J. Brockwell and R. A. Davis, *Time Series: Theory and Methods*, Springer, 1991, §7.1.
* A. Aue, *Time Series Analysis*, §2.1, "Estimation of the Mean".
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.SummableCovarianceMean

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma abs_cov_eq {Z : ℕ → Ω → ℝ} {γ : ℕ → ℝ}
    (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h) (i j : ℕ) :
    |cov[Z i, Z j; P]| = if j ≤ i then |γ (i - j)| else |γ (j - i)| := by
  split_ifs with h
  · rw [covariance_comm, show i = j + (i - j) by omega, hγ, show j + (i - j) - j = i - j by omega]
  · rw [show j = i + (j - i) by omega, hγ, show i + (j - i) - i = j - i by omega]

omit [IsProbabilityMeasure P] in
private lemma gamma_zero_nonneg {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {γ : ℕ → ℝ}
    (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h) : 0 ≤ γ 0 := by
  have h := hγ 0 0
  simp only [add_zero] at h
  rw [← h, covariance_self (hZ 0).aestronglyMeasurable.aemeasurable]
  exact variance_nonneg _ _

omit [IsProbabilityMeasure P] in
private lemma row_le {Z : ℕ → Ω → ℝ} {γ : ℕ → ℝ} (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h)
    (hsum : Summable fun h => |γ h|) (h0 : 0 ≤ γ 0) (L i : ℕ) :
    ∑ j ∈ range L, |cov[Z i, Z j; P]| ≤ γ 0 + 2 * ∑' h, |γ (h + 1)| := by
  have hs1 : Summable fun h => |γ (h + 1)| := (summable_nat_add_iff 1).2 hsum
  have hT : ∀ n, ∑ h ∈ range n, |γ (h + 1)| ≤ ∑' h, |γ (h + 1)| := fun n =>
    hs1.sum_le_tsum _ fun h _ => abs_nonneg _
  simp_rw [abs_cov_eq hγ i]
  rw [← sum_filter_add_sum_filter_not (range L) (· ≤ i)]
  have hf1 : (range L).filter (· ≤ i) = range (min (i + 1) L) := by
    ext j; simp; omega
  have hf2 : (range L).filter (fun j => ¬ j ≤ i) = Ico (i + 1) L := by
    ext j; simp; omega
  rw [hf1, hf2]
  have hA : ∑ j ∈ range (min (i + 1) L), (if j ≤ i then |γ (i - j)| else |γ (j - i)|) ≤
      γ 0 + ∑' h, |γ (h + 1)| := by
    calc ∑ j ∈ range (min (i + 1) L), (if j ≤ i then |γ (i - j)| else |γ (j - i)|)
        = ∑ j ∈ range (min (i + 1) L), |γ (i - j)| := by
          refine sum_congr rfl fun j hj => ?_
          rw [ite_eq_left_iff.2 fun h => absurd (by simp at hj; omega) h]
      _ ≤ ∑ j ∈ range (i + 1), |γ (i - j)| :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (min_le_left _ _))
            fun _ _ _ => abs_nonneg _
      _ = ∑ h ∈ range (i + 1), |γ h| := by
          rw [← sum_range_reflect]
          refine sum_congr rfl fun j hj => ?_
          simp at hj
          congr 2
          omega
      _ = |γ 0| + ∑ h ∈ range i, |γ (h + 1)| := by rw [sum_range_succ', add_comm]
      _ ≤ γ 0 + ∑' h, |γ (h + 1)| := by
          rw [abs_of_nonneg h0]; linarith [hT i]
  have hB : ∑ j ∈ Ico (i + 1) L, (if j ≤ i then |γ (i - j)| else |γ (j - i)|) ≤
      ∑' h, |γ (h + 1)| := by
    calc ∑ j ∈ Ico (i + 1) L, (if j ≤ i then |γ (i - j)| else |γ (j - i)|)
        = ∑ j ∈ Ico (i + 1) L, |γ (j - i)| := by
          refine sum_congr rfl fun j hj => ?_
          rw [ite_eq_right_iff.2 fun h => absurd h (by simp at hj; omega)]
      _ = ∑ h ∈ range (L - (i + 1)), |γ (h + 1)| := by
          rw [sum_Ico_eq_sum_range]
          refine sum_congr rfl fun h _ => ?_
          congr 2
          omega
      _ ≤ ∑' h, |γ (h + 1)| := hT _
  linarith

theorem variance_mean_le {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {γ : ℕ → ℝ}
    (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h) (hsum : Summable fun h => |γ h|) (L : ℕ) :
    Var[fun ω => (L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω; P] ≤
      (γ 0 + 2 * ∑' h, |γ (h + 1)|) / L := by
  have h0 := gamma_zero_nonneg hZ hγ
  set C := γ 0 + 2 * ∑' h, |γ (h + 1)| with hC
  rw [variance_const_mul, variance_fun_sum' fun i _ => hZ i]
  have hS : ∑ i ∈ range L, ∑ j ∈ range L, cov[Z i, Z j; P] ≤ L * C := by
    calc ∑ i ∈ range L, ∑ j ∈ range L, cov[Z i, Z j; P]
        ≤ ∑ i ∈ range L, ∑ j ∈ range L, |cov[Z i, Z j; P]| :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ _i ∈ range L, C := sum_le_sum fun i _ => row_le hγ hsum h0 L i
      _ = L * C := by simp
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    calc ((L : ℝ)⁻¹) ^ 2 * ∑ i ∈ range L, ∑ j ∈ range L, cov[Z i, Z j; P]
        ≤ ((L : ℝ)⁻¹) ^ 2 * (L * C) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = C / L := by field_simp

omit [IsProbabilityMeasure P] in
private lemma memLp_mean {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) (L : ℕ) :
    MemLp (fun ω => (L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω) 2 P := by
  have : MemLp (fun ω => ∑ i ∈ range L, Z i ω) 2 P := by
    have h := memLp_finsetSum' (range L) fun i _ => hZ i
    convert h using 1
    ext ω
    simp [Finset.sum_apply]
  exact this.const_mul _

private lemma integral_mean {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {m : ℝ}
    (hm : ∀ i, P[Z i] = m) {L : ℕ} (hL : L ≠ 0) :
    P[fun ω => (L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω] = m := by
  rw [integral_const_mul, integral_finsetSum _ fun i _ => (hZ i).integrable one_le_two]
  simp only [hm, sum_const, card_range, nsmul_eq_mul]
  field_simp

theorem tendsto_integral_sq_mean_sub {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {m : ℝ}
    (hm : ∀ i, P[Z i] = m) {γ : ℕ → ℝ} (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h)
    (hsum : Summable fun h => |γ h|) :
    Tendsto (fun L : ℕ => ∫ ω, ((L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω - m) ^ 2 ∂P) atTop (𝓝 0) := by
  set C := γ 0 + 2 * ∑' h, |γ (h + 1)|
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat C) ?_ ?_
  · exact Eventually.of_forall fun L => integral_nonneg fun ω => sq_nonneg _
  · refine eventually_atTop.2 ⟨1, fun L hL => ?_⟩
    have hv := variance_mean_le hZ hγ hsum L
    rw [variance_eq_integral (memLp_mean hZ L).aestronglyMeasurable.aemeasurable,
      integral_mean hZ hm (by omega)] at hv
    exact hv

private lemma meas_dev_le {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {m : ℝ}
    (hm : ∀ i, P[Z i] = m) {γ : ℕ → ℝ} (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h)
    (hsum : Summable fun h => |γ h|) {c : ℝ} (hc : 0 < c) {L : ℕ} (hL : L ≠ 0) :
    P {ω | c ≤ |(L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω - m|} ≤
      ENNReal.ofReal ((γ 0 + 2 * ∑' h, |γ (h + 1)|) / L / c ^ 2) := by
  have h := meas_ge_le_variance_div_sq (memLp_mean hZ L) hc
  rw [integral_mean hZ hm hL] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right (variance_mean_le hZ hγ hsum L) (by positivity)

private lemma tendsto_meas_dev {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {m : ℝ}
    (hm : ∀ i, P[Z i] = m) {γ : ℕ → ℝ} (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h)
    (hsum : Summable fun h => |γ h|) {ε : ℝ≥0∞} (hε : 0 < ε) (hεt : ε ≠ ∞) :
    Tendsto (fun L : ℕ => P {ω | ε ≤ edist ((L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω) m}) atTop
      (𝓝 0) := by
  set c := ε.toReal
  have hc : 0 < c := ENNReal.toReal_pos hε.ne' hεt
  have hset : ∀ L : ℕ, {ω | ε ≤ edist ((L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω) m} =
      {ω | c ≤ |(L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω - m|} := by
    intro L
    ext ω
    simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal hεt, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  simp_rw [hset]
  set C := γ 0 + 2 * ∑' h, |γ (h + 1)|
  have hup : Tendsto (fun L : ℕ => ENNReal.ofReal (C / L / c ^ 2)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).div_const (c ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  exact eventually_atTop.2 ⟨1, fun L hL => meas_dev_le hZ hm hγ hsum hc (by omega)⟩

theorem tendstoInMeasure_mean {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {m : ℝ}
    (hm : ∀ i, P[Z i] = m) {γ : ℕ → ℝ} (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h)
    (hsum : Summable fun h => |γ h|) :
    TendstoInMeasure P (fun (L : ℕ) ω => (L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω) atTop
      (fun _ => m) :=
  tendstoInMeasure_of_ne_top fun _ hε hεt => tendsto_meas_dev hZ hm hγ hsum hε hεt

theorem tendstoInMeasure_mean_pi {d : ℕ} {Z : ℕ → Ω → (Fin d → ℝ)}
    (hZ : ∀ i j, MemLp (fun ω => Z i ω j) 2 P) {m : Fin d → ℝ}
    (hm : ∀ i j, P[fun ω => Z i ω j] = m j) {γ : Fin d → ℕ → ℝ}
    (hγ : ∀ j i h, cov[fun ω => Z i ω j, fun ω => Z (i + h) ω j; P] = γ j h)
    (hsum : ∀ j, Summable fun h => |γ j h|) :
    TendstoInMeasure P (fun (L : ℕ) ω => (L : ℝ)⁻¹ • ∑ i ∈ range L, Z i ω) atTop
      (fun _ => m) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
  have hcoord : ∀ (L : ℕ) (ω : Ω) (j : Fin d),
      ((L : ℝ)⁻¹ • ∑ i ∈ range L, Z i ω) j = (L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω j := by
    intro L ω j
    simp [Finset.sum_apply]
  have hsub : ∀ L : ℕ, {ω | ε ≤ edist ((L : ℝ)⁻¹ • ∑ i ∈ range L, Z i ω) m} ⊆
      ⋃ j, {ω | ε ≤ edist ((L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω j) (m j)} := by
    intro L ω hω
    simp only [Set.mem_ofPred_eq, edist_pi_def] at hω
    obtain ⟨j, -, hj⟩ := (Finset.le_sup_iff hε).1 hω
    exact Set.mem_iUnion.2 ⟨j, by simpa [hcoord] using hj⟩
  have hsum' : Tendsto (fun L : ℕ => ∑ j, P {ω | ε ≤ edist ((L : ℝ)⁻¹ * ∑ i ∈ range L, Z i ω j)
      (m j)}) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _j : Fin d, 0 by simp]
    exact tendsto_finsetSum _ fun j _ =>
      tendsto_meas_dev (Z := fun i ω => Z i ω j) (fun i => hZ i j) (fun i => hm i j) (hγ j)
        (hsum j) hε hεt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum'
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun L => ?_)
  exact (measure_mono (hsub L)).trans (measure_iUnion_fintype_le _ _)

end MathlibExt.Probability.Statistics.SummableCovarianceMean
