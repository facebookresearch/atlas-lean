/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.AMSSketch
public import MathlibExt.Probability.MedianOfMeans

/-!
# The Alon–Matias–Szegedy estimator for `F₂`: median of means

Alon, Matias and Szegedy estimate the second frequency moment `F₂` of a stream by `s₂` means
`Y₁, …, Y_{s₂}`, each the average of `s₁` independent copies of the squared sketch `Z²`, and
output the median of the means. With `s₁ ≥ 16 / λ²`, Chebyshev's inequality and
`Var(Z²) ≤ 2 F₂²` make each mean a `(1 ± λ)`-approximation with probability at least `7 / 8`,
and the median trick makes the failure probability exponentially small in `s₂` (N. Alon,
Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments",
J. Comput. System Sci. 58 (1999) 137–147, Theorem 2.2 and its proof).

## Main results

- `measureReal_mean_notMem_Icc_le`: the Chebyshev step for one mean.
- `measureReal_ams_estimate_le`: the probability that the median of means deviates from `F₂`
  by more than `λ F₂` is at most `exp (-9 s₂ / 32)`.

The space bound of Theorem 2.2 (`O(log (1/ε) λ⁻² (log n + log m))` bits, using an explicit
four-wise independent family of size `O(n²)`) is not formalized here: the statements are about
the estimator's distribution, for any family of signs with the stated independence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real

namespace MathlibExt.Probability.Streaming.AMS

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace Ω] [DecidableEq ι] in
private theorem abs_weightedSum_sq_le {ε : ι → Ω → ℝ}
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (m : ι → ℝ) (ω : Ω) :
    |(∑ i, m i * ε i ω) ^ 2| ≤ (∑ i, |m i|) ^ 2 := by
  rw [abs_pow]
  have : |∑ i, m i * ε i ω| ≤ ∑ i, |m i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have : |ε i ω| = 1 := by rcases hsign i ω with h | h <;> rw [h] <;> norm_num
    rw [this, mul_one]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

omit [DecidableEq ι] in
private theorem memLp_weightedSum_sq {ε : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (m : ι → ℝ) :
    MemLp (fun ω => (∑ i, m i * ε i ω) ^ 2) 2 μ :=
  MemLp.of_bound ((Finset.measurable_fun_sum _ fun i _ =>
    measurable_const.mul (hmeas i)).pow_const 2).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_weightedSum_sq_le hsign m ω)

omit [DecidableEq ι] in
/-- **Chebyshev step for one mean of AMS estimators.** Let `ε k` (`k < s₁`) be families of
measurable `±1`-valued, mean-zero, four-wise independent signs, with the `s₁` families mutually
independent, and let `mᵢ` be real weights with `F = ∑ᵢ mᵢ²`. If `λ > 0` and `s₁ ≥ 16 / λ²`, the
mean `Y = (1 / s₁) ∑_k (∑ᵢ mᵢ ε_{k,i})²` lies outside `[F - λF, F + λF]` with probability at most
`1 / 8` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of
Theorem 2.2: `Prob[|Yᵢ - F₂| > λ F₂] ≤ 2 F₂² / (s₁ λ² F₂²) = 1 / 8`). -/
theorem measureReal_mean_notMem_Icc_le {s₁ : ℕ} (ε : Fin s₁ → ι → Ω → ℝ)
    (hmeas : ∀ k i, Measurable (ε k i)) (hsign : ∀ k i ω, ε k i ω = 1 ∨ ε k i ω = -1)
    (hmean : ∀ k i, μ[ε k i] = 0) (hfour : ∀ k, FourWiseIndependent (ε k) μ)
    (hcol : iIndepFun (fun k ω => fun i => ε k i ω) μ) (m : ι → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hs₁ : 16 / lam ^ 2 ≤ s₁) :
    μ.real {ω | (1 / s₁ : ℝ) * ∑ k, (∑ i, m i * ε k i ω) ^ 2 ∉
      Set.Icc (∑ i, m i ^ 2 - lam * ∑ i, m i ^ 2) (∑ i, m i ^ 2 + lam * ∑ i, m i ^ 2)} ≤
        1 / 8 := by
  classical
  set F := ∑ i, m i ^ 2 with hF
  have hs₁pos : (0 : ℝ) < s₁ := lt_of_lt_of_le (by positivity) hs₁
  set X : Fin s₁ → Ω → ℝ := fun k ω => (∑ i, m i * ε k i ω) ^ 2 with hX
  set Y : Ω → ℝ := fun ω => (1 / s₁ : ℝ) * ∑ k, X k ω with hY
  rcases (show 0 ≤ F by positivity).eq_or_lt with hF0 | hFpos
  · -- `F = 0`: all weights vanish and the mean is identically `0 = F`.
    have hm : ∀ i, m i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (m i))).1 hF0.symm i
        (mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : {ω | (1 / s₁ : ℝ) * ∑ k, (∑ i, m i * ε k i ω) ^ 2 ∉
        Set.Icc (F - lam * F) (F + lam * F)} = ∅ := by
      ext ω
      simp [hm, ← hF0]
    rw [this, measureReal_empty]
    norm_num
  have hXL2 : ∀ k, MemLp (X k) 2 μ := fun k => memLp_weightedSum_sq (hmeas k) (hsign k) m
  have hXmean : ∀ k, μ[X k] = F := fun k =>
    integral_sq_weightedSum (hmeas k) (hsign k) (hmean k) (hfour k) m
  have hXvar : ∀ k, variance (X k) μ ≤ 2 * F ^ 2 := fun k =>
    variance_sq_weightedSum_le (hmeas k) (hsign k) (hmean k) (hfour k) m
  -- Independence of the copies.
  have hXind : iIndepFun X μ := by
    have := hcol.comp (fun _ v => (∑ i, m i * v i) ^ 2) fun _ => by fun_prop
    exact this
  have hYL2 : MemLp Y 2 μ := by
    have : MemLp (∑ k, X k) 2 μ := memLp_finsetSum' _ fun k _ => hXL2 k
    have h2 := this.const_mul (1 / s₁ : ℝ)
    convert h2 using 1
    funext ω
    simp [hY, Finset.sum_apply]
  have hYmean : μ[Y] = F := by
    simp only [hY]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (hXL2 k).integrable one_le_two]
    simp only [hXmean, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hYvar : variance Y μ ≤ 2 * F ^ 2 / s₁ := by
    have hsumvar : variance (∑ k, X k) μ = ∑ k, variance (X k) μ :=
      IndepFun.variance_sum (fun k _ => hXL2 k) fun k _ l _ hkl => hXind.indepFun hkl
    have hYeq : Y = fun ω => (1 / s₁ : ℝ) * (∑ k, X k) ω := by
      funext ω; simp [hY, Finset.sum_apply]
    rw [hYeq, variance_const_mul, hsumvar]
    calc (1 / s₁ : ℝ) ^ 2 * ∑ k, variance (X k) μ ≤ (1 / s₁ : ℝ) ^ 2 * ∑ _k : Fin s₁, 2 * F ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hXvar k) (by positivity)
      _ = 2 * F ^ 2 / s₁ := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hc : 0 < lam * F := mul_pos hlam hFpos
  have hcheb := meas_ge_le_variance_div_sq hYL2 hc
  rw [hYmean] at hcheb
  have hsub : {ω | (1 / s₁ : ℝ) * ∑ k, (∑ i, m i * ε k i ω) ^ 2 ∉
      Set.Icc (F - lam * F) (F + lam * F)} ⊆ {ω | lam * F ≤ |Y ω - F|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hω ⊢
    rw [le_abs]
    rcases hω with h | h
    · right; simp only [hY, hX]; linarith
    · left; simp only [hY, hX]; linarith
  have hbound : variance Y μ / (lam * F) ^ 2 ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    calc variance Y μ ≤ 2 * F ^ 2 / s₁ := hYvar
      _ ≤ 1 / 8 * (lam * F) ^ 2 := by
          rw [div_le_iff₀ hs₁pos]
          have : 16 ≤ s₁ * lam ^ 2 := by
            rw [div_le_iff₀ (by positivity)] at hs₁; linarith
          nlinarith [sq_nonneg F, sq_nonneg lam]
  calc μ.real _ ≤ μ.real {ω | lam * F ≤ |Y ω - F|} := measureReal_mono hsub
    _ ≤ variance Y μ / (lam * F) ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)) hcheb
    _ ≤ 1 / 8 := hbound

/-- **The AMS estimator for `F₂`.** Let `ε j k` (`j < s₂`, `k < s₁`) be families of measurable
`±1`-valued, mean-zero, four-wise independent signs indexed by `ι`, such that the `s₂` blocks
`(ε j k)_k` are mutually independent and, inside each block, the `s₁` families are mutually
independent. For a stream `l`, let `Yⱼ = (1 / s₁) ∑_k Z_{jk}²` with `Z_{jk}` the AMS sketch of
`l` under the signs `ε j k`, and let `Y` be the median of `Y₁, …, Y_{s₂}`. If `λ > 0` and
`s₁ ≥ 16 / λ²`, then `Prob[|Y - F₂(l)| > λ F₂(l)] ≤ exp (-9 s₂ / 32)`.

This is the probabilistic content of N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58
(1999), Theorem 2.2, whose proof takes `s₁ = 16 / λ²` and `s₂ = 2 log (1 / ε)` and bounds the
median step by a Chernoff estimate; here the median step uses Hoeffding's inequality, so
`s₂ ≥ (32 / 9) log (1 / ε)` gives failure probability at most `ε`. The space bound of the theorem
is not part of this statement. -/
theorem measureReal_ams_estimate_le {s₁ s₂ : ℕ} (ε : Fin s₂ → Fin s₁ → ι → Ω → ℝ)
    (hmeas : ∀ j k i, Measurable (ε j k i))
    (hsign : ∀ j k i ω, ε j k i ω = 1 ∨ ε j k i ω = -1)
    (hmean : ∀ j k i, μ[ε j k i] = 0) (hfour : ∀ j k, FourWiseIndependent (ε j k) μ)
    (hrow : iIndepFun (fun j ω => fun k i => ε j k i ω) μ)
    (hcol : ∀ j, iIndepFun (fun k ω => fun i => ε j k i ω) μ)
    {lam : ℝ} (hlam : 0 < lam) (hs₁ : 16 / lam ^ 2 ≤ s₁) (l : List ι) :
    μ.real {ω | lam * secondMoment l < |MedianOfMeans.sampleMedian
        (fun j => (1 / s₁ : ℝ) * ∑ k, sketch (ε j k) l ω ^ 2) - secondMoment l|} ≤
      exp (-9 * s₂ / 32) := by
  set m : ι → ℝ := freq l with hm
  set F := secondMoment l with hF
  have hFm : F = ∑ i, m i ^ 2 := rfl
  set Y : Fin s₂ → Ω → ℝ := fun j ω => (1 / s₁ : ℝ) * ∑ k, (∑ i, m i * ε j k i ω) ^ 2 with hY
  have hYind : iIndepFun Y μ :=
    hrow.comp (fun _ v => (1 / s₁ : ℝ) * ∑ k, (∑ i, m i * v k i) ^ 2) fun _ => by fun_prop
  have hYmeas : ∀ j, Measurable (Y j) := fun j => by
    simp only [hY]
    exact measurable_const.mul (Finset.measurable_fun_sum _ fun k _ =>
      (Finset.measurable_fun_sum _ fun i _ => measurable_const.mul (hmeas j k i)).pow_const 2)
  have hbad : ∀ j, μ.real {ω | Y j ω ∉ Set.Icc (F - lam * F) (F + lam * F)} ≤ 1 / 8 :=
    fun j => measureReal_mean_notMem_Icc_le (ε j) (hmeas j) (hsign j) (hmean j) (hfour j)
      (hcol j) m hlam hs₁
  have hmed := MedianOfMeans.measureReal_sampleMedian_notMem_Icc_le hYind hYmeas hbad
  refine le_trans (measureReal_mono fun ω hω => ?_) hmed
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hω ⊢
  have hYω : (fun j => Y j ω) = fun j => (1 / s₁ : ℝ) * ∑ k, sketch (ε j k) l ω ^ 2 := by
    funext j; simp only [hY, sketch_eq_sum_count_mul, hm]
  rw [hYω]
  rcases lt_abs.1 hω with h | h
  · right; linarith
  · left; linarith

end MathlibExt.Probability.Streaming.AMS
