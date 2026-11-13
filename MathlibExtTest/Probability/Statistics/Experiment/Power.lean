/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Power

/-!
# Tests for the law of the known-variance z statistic

Null-case collapse to the standard normal, the variance identity, and the
single-observation shape.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Experiment

/-- Use: at the null `μ = μ0` the statistic is standard normal. -/
example {n : ℕ} (hn : 0 < n) (μ0 : ℝ) {v : NNReal} (hv : v ≠ 0) :
    HasLaw (zStat n μ0 v) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal μ0 v) := by
  have h := hasLaw_zStat hn μ0 μ0 hv
  simpa using h

/-- Use: the variance computation at the heart of the proof. -/
example {n : ℕ} (hn : 0 < n) {v : NNReal} (hv : v ≠ 0) :
    (Real.sqrt (n : ℝ) / Real.sqrt (v : ℝ)) ^ 2 * ((v : ℝ) / (n : ℝ)) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt v.coe_nonneg]
  field_simp

/-- Boundary: at `n = 1` the statistic is the single standardized observation. -/
example (μ0 : ℝ) (v : NNReal) (x : Fin 1 → ℝ) :
    zStat 1 μ0 v x = (x 0 - μ0) / Real.sqrt (v : ℝ) := by
  simp [zStat]

/-- Use: at `δ = 0` the rejection probability is the nominal tail `1 - Φ(c)`. -/
example {n : ℕ} (hn : 0 < n) (μ0 c : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal μ0 v).real (zTestReject n μ0 v c)
      = 1 - cdf (gaussianReal 0 1) c := by
  have h := measureReal_zTestReject hn μ0 0 c hv
  simp only [add_zero, mul_zero, zero_div, sub_zero] at h
  exact h

/-- Boundary: the rejection probability always lies in `[0, 1]`. -/
example {n : ℕ} (_hn : 0 < n) (μ0 δ c : ℝ) {v : NNReal} (_hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real (zTestReject n μ0 v c)
      ∈ Set.Icc 0 1 := by
  rw [Set.mem_Icc]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Control: strict and non-strict cutoffs differ in general (the atom case), so the rejection
set keeps the strict form. -/
example (c : ℝ) : {x : Fin 1 → ℝ | c < x 0} ≠ {x : Fin 1 → ℝ | c ≤ x 0} := by
  intro hcon
  have hmem : (fun _ : Fin 1 => c) ∈ {x : Fin 1 → ℝ | c ≤ x 0} := le_refl c
  rw [← hcon] at hmem
  exact lt_irrefl c hmem

/-- Boundary: at `δ = 0` and cutoff `c = 0` the power is `1 / 2`. -/
example {n : ℕ} (hn : 0 < n) (μ0 : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal μ0 v).real (zTestReject n μ0 v 0) = 1 / 2 := by
  have h := measureReal_zTestReject_eq_cdf hn μ0 0 (0 : ℝ) hv
  simp only [add_zero, mul_zero, zero_div, sub_zero, cdf_gaussianReal_zero] at h
  exact h

/-- Use: at `δ = 0` the power is the size `Φ(-c)`. -/
example {n : ℕ} (hn : 0 < n) (μ0 c : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal μ0 v).real (zTestReject n μ0 v c)
      = cdf (gaussianReal 0 1) (-c) := by
  have h := measureReal_zTestReject_eq_cdf hn μ0 0 c hv
  simp only [add_zero, mul_zero, zero_div, zero_sub] at h
  exact h

/-- Use: for a positive shift, a larger known variance gives strictly lower power. -/
example {n : ℕ} (hn : 0 < n) (μ0 c : ℝ) {δ : ℝ} (hδ : 0 < δ) {v w : NNReal} (hv : v ≠ 0)
    (hvw : v < w) :
    (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) w).real (zTestReject n μ0 w c)
      < (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real (zTestReject n μ0 v c) := by
  have hw : w ≠ 0 := by
    intro h
    subst h
    exact absurd (lt_of_le_of_lt zero_le hvw) (lt_irrefl _)
  rw [measureReal_zTestReject_eq_cdf hn μ0 δ c hw,
    measureReal_zTestReject_eq_cdf hn μ0 δ c hv]
  have hnum : 0 < Real.sqrt (n : ℝ) * δ :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn)) hδ
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : NNReal) < v := lt_of_le_of_ne zero_le (Ne.symm hv)
    exact_mod_cast h
  have hwpos : (0 : ℝ) < (w : ℝ) := by
    have h : (0 : NNReal) < w := lt_of_le_of_lt zero_le hvw
    exact_mod_cast h
  have hsqrt : Real.sqrt (v : ℝ) < Real.sqrt (w : ℝ) :=
    Real.sqrt_lt_sqrt (le_of_lt hvpos) (by exact_mod_cast hvw)
  have hlt : Real.sqrt (n : ℝ) * δ / Real.sqrt (w : ℝ) - c
      < Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ) - c := by
    rw [sub_lt_sub_iff_right,
      div_lt_div_iff_of_pos_left hnum (Real.sqrt_pos.mpr hwpos) (Real.sqrt_pos.mpr hvpos)]
    exact hsqrt
  exact strictMono_cdf_gaussianReal 0 one_ne_zero hlt

/-- Use (equality case): `n = ⌈(√v (z_α + z_β) / δ)²⌉` itself is certified; its positivity
follows from the other hypotheses, so no `0 < n` premise is needed. -/
theorem samplesize_eq_ceil_certified {α β δ μ0 : ℝ} {v : NNReal}
    (hα : α ∈ Set.Ioo 0 (1 / 2))
    (hβ : β ∈ Set.Ioo 0 (1 / 2)) (hδ : 0 < δ) (hv : v ≠ 0) :
    1 - β ≤ (Measure.pi fun _ : Fin ⌈(Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1)
        (1 - α) + cdfQuantile (gaussianReal 0 1) (1 - β)) / δ) ^ 2⌉₊ =>
          gaussianReal (μ0 + δ) v).real
      (zTestReject ⌈(Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α)
        + cdfQuantile (gaussianReal 0 1) (1 - β)) / δ) ^ 2⌉₊ μ0 v
        (cdfQuantile (gaussianReal 0 1) (1 - α))) := by
  have hzα : 0 < cdfQuantile (gaussianReal 0 1) (1 - α) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hα
    exact ⟨by linarith, by linarith⟩
  have hzβ : 0 < cdfQuantile (gaussianReal 0 1) (1 - β) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hβ
    exact ⟨by linarith, by linarith⟩
  have hvR : 0 < (v : ℝ) := by
    have h : (0 : NNReal) < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast h
  refine power_ge_of_le_ceil hα hβ hδ hv ?_ le_rfl
  exact Nat.ceil_pos.mpr (pow_pos (div_pos (mul_pos (Real.sqrt_pos.mpr hvR)
    (add_pos hzα hzβ)) hδ) 2)

/-- Boundary: at `α = β = 49/100`, just inside the `(0, 1/2)` window, the certificate still
guarantees power at least `51/100`. -/
theorem samplesize_alpha_beta_near_half {δ μ0 : ℝ} {v : NNReal} (hδ : 0 < δ) (hv : v ≠ 0)
    {n : ℕ} (hn : 0 < n)
    (hN : ⌈(Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - 49 / 100)
        + cdfQuantile (gaussianReal 0 1) (1 - 49 / 100)) / δ) ^ 2⌉₊ ≤ n) :
    (51 / 100 : ℝ) ≤ (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real
      (zTestReject n μ0 v (cdfQuantile (gaussianReal 0 1) (1 - 49 / 100))) := by
  have hα : (49 / 100 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  have hβ : (49 / 100 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  have h := power_ge_of_le_ceil (μ0 := μ0) hα hβ hδ hv hn hN
  linarith

/-- Use: a sample size certified for a larger known variance `w` is certified for any smaller
nonzero variance `v` (the bound is monotone in the variance). -/
theorem samplesize_mono_variance {α β δ μ0 : ℝ} {v w : NNReal}
    (hα : α ∈ Set.Ioo 0 (1 / 2))
    (hβ : β ∈ Set.Ioo 0 (1 / 2)) (hδ : 0 < δ) (hv : v ≠ 0) (hvw : v ≤ w) {n : ℕ} (hn : 0 < n)
    (hN : ⌈(Real.sqrt (w : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α)
        + cdfQuantile (gaussianReal 0 1) (1 - β)) / δ) ^ 2⌉₊ ≤ n) :
    1 - β ≤ (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real
      (zTestReject n μ0 v (cdfQuantile (gaussianReal 0 1) (1 - α))) := by
  have hzα : 0 < cdfQuantile (gaussianReal 0 1) (1 - α) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hα
    exact ⟨by linarith, by linarith⟩
  have hzβ : 0 < cdfQuantile (gaussianReal 0 1) (1 - β) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hβ
    exact ⟨by linarith, by linarith⟩
  have hAB : 0 ≤ cdfQuantile (gaussianReal 0 1) (1 - α) +
      cdfQuantile (gaussianReal 0 1) (1 - β) := le_of_lt (add_pos hzα hzβ)
  have hvwR : (v : ℝ) ≤ (w : ℝ) := by exact_mod_cast hvw
  have hsqrt : Real.sqrt (v : ℝ) ≤ Real.sqrt (w : ℝ) := Real.sqrt_le_sqrt hvwR
  have hmul : Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α) +
      cdfQuantile (gaussianReal 0 1) (1 - β)) ≤ Real.sqrt (w : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) :=
    mul_le_mul_of_nonneg_right hsqrt hAB
  have hle : Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α) +
      cdfQuantile (gaussianReal 0 1) (1 - β)) / δ ≤ Real.sqrt (w : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) / δ :=
    div_le_div_of_nonneg_right hmul (le_of_lt hδ)
  have hnonneg : 0 ≤ Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α) +
      cdfQuantile (gaussianReal 0 1) (1 - β)) / δ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hAB) (le_of_lt hδ)
  refine power_ge_of_le_ceil hα hβ hδ hv hn (le_trans (Nat.ceil_mono ?_) hN)
  exact pow_le_pow_left₀ hnonneg hle 2

/-- Negative: at `β = 1/2` the quantile `z_β` is not positive, so the open upper end of `hβ`
is exactly where the positivity step of the route stops. -/
theorem samplesize_zBeta_half_nonpos : cdfQuantile (gaussianReal 0 1) (1 - 1 / 2) ≤ 0 := by
  have h : (1 - 1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  rw [cdfQuantile_le_iff _ h, cdf_gaussianReal_zero]
  norm_num

end MathlibExt.Probability.Statistics.Experiment
