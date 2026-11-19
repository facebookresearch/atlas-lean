/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.Generalizability

/-!
# Tests for crossed-design error variances

Small person/item instances with unit and unequal variances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics.Measurement

/-- two persons, one item, and unit residual variance.

The person and item variance components are `0` and the residual
variance component is `1`, so both error variances are `1`.  Centering
a residual by the mean over the two sampled persons instead has
variance `1 / 2`, not `1`: the errors above are centered by the model
mean `grandMean + P p`, not by a sampled person mean. -/
theorem pin_test_two_persons_one_item_unit_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (grandMean : ℝ)
    (X : Fin 2 → Fin 1 → Ω → ℝ) (P : Fin 2 → Ω → ℝ)
    (I : Fin 1 → Ω → ℝ) (e : Fin 2 → Fin 1 → Ω → ℝ)
    (p : Fin 2)
    (hX : ∀ p i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hP_mem : ∀ p, MemLp (P p) 2 μ)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ p i, MemLp (e p i) 2 μ)
    (hP_mean : ∀ p, μ[P p] = 0)
    (hI_mean : ∀ i, μ[I i] = 0)
    (he_mean : ∀ p i, μ[e p i] = 0)
    (hP_cov : ∀ p q, cov[P p, P q; μ]
      = if p = q then (0 : ℝ) else 0)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then (0 : ℝ) else 0)
    (he_cov : ∀ p i q j, cov[e p i, e q j; μ]
      = if (p, i) = (q, j) then (1 : ℝ) else 0)
    (hPI_cov : ∀ p i, cov[P p, I i; μ] = 0)
    (hIP_cov : ∀ i p, cov[I i, P p; μ] = 0)
    (hPe_cov : ∀ p q i, cov[P p, e q i; μ] = 0)
    (heP_cov : ∀ p i q, cov[e p i, P q; μ] = 0)
    (hIe_cov : ∀ i p j, cov[I i, e p j; μ] = 0)
    (heI_cov : ∀ p i j, cov[e p i, I j; μ] = 0) :
    Var[Delta_p grandMean X P p; μ] = 1
      ∧ Var[delta_p grandMean X P I p; μ] = 1
      ∧ Var[fun ω => e p 0 ω - (e 0 0 ω + e 1 0 ω) / 2; μ] = 1 / 2
      ∧ Var[fun ω => e p 0 ω - (e 0 0 ω + e 1 0 ω) / 2; μ]
        ≠ Var[delta_p grandMean X P I p; μ] := by
  have hm_pos : 0 < (Fintype.card (Fin 1) : ℝ) := by simp
  have hmain := variance_absolute_relative_errors grandMean X P I e 0 0 1 p
    hX hP_mem hI_mem he_mem hP_mean hI_mean he_mean hP_cov hI_cov he_cov
    hPI_cov hIP_cov hPe_cov heP_cov hIe_cov heI_cov
    le_rfl le_rfl zero_le_one hm_pos
  simp at hmain
  obtain ⟨hDelta, hdelta⟩ := hmain
  have h00 : MemLp (e 0 0) 2 μ := he_mem 0 0
  have h10 : MemLp (e 1 0) 2 μ := he_mem 1 0
  have hvar00 : Var[e 0 0; μ] = 1 := by
    have h := he_cov 0 0 0 0
    simp at h
    rw [← h, ← covariance_self h00.aemeasurable]
  have hvar10 : Var[e 1 0; μ] = 1 := by
    have h := he_cov 1 0 1 0
    simp at h
    rw [← h, ← covariance_self h10.aemeasurable]
  have hcov01 : cov[e 0 0, e 1 0; μ] = 0 := by
    have h := he_cov 0 0 1 0
    simp at h
    exact h
  have hcov10 : cov[e 1 0, e 0 0; μ] = 0 := by
    have h := he_cov 1 0 0 0
    simp at h
    exact h
  have hcenter : Var[fun ω => e p 0 ω - (e 0 0 ω + e 1 0 ω) / 2; μ] = 1 / 2 := by
    fin_cases p
    · simp only [Fin.mk_zero]
      have hfun : (fun ω => e 0 0 ω - (e 0 0 ω + e 1 0 ω) / 2)
          = fun ω => (1 / 2) * (e 0 0 ω - e 1 0 ω) := by
        funext ω
        ring
      rw [hfun, variance_const_mul, variance_fun_sub h00 h10, hvar00, hvar10, hcov01]
      norm_num
    · simp only [Fin.mk_one]
      have hfun : (fun ω => e 1 0 ω - (e 0 0 ω + e 1 0 ω) / 2)
          = fun ω => (1 / 2) * (e 1 0 ω - e 0 0 ω) := by
        funext ω
        ring
      rw [hfun, variance_const_mul, variance_fun_sub h10 h00, hvar10, hvar00, hcov10]
      norm_num
  refine ⟨hDelta, hdelta, hcenter, ?_⟩
  rw [hcenter, hdelta]
  norm_num

/-- unequal item variances and the variance of a mean.

Two uncorrelated square-integrable variables with variances `1` and
`9` have a two-term mean of variance `(1 + 9) / 4 = 5 / 2`.  This is
the general covariance-sum computation of which the common-variance
item mean above is the equal-variance case. -/
theorem pin_test_unequal_item_variances_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (Y : Fin 2 → Ω → ℝ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ)
    (hY0 : Var[Y 0; μ] = 1) (hY1 : Var[Y 1; μ] = 9)
    (hY_cov : cov[Y 0, Y 1; μ] = 0) :
    Var[fun ω => (Y 0 ω + Y 1 ω) / 2; μ] = 5 / 2 := by
  have hfun : (fun ω => (Y 0 ω + Y 1 ω) / 2)
      = fun ω => (1 / 2) * (Y 0 ω + Y 1 ω) := by
    funext ω
    ring
  rw [hfun, variance_const_mul, variance_fun_add (hY_mem 0) (hY_mem 1), hY0, hY1, hY_cov]
  norm_num

/-- shared item effects correlate different persons.

With two persons, one item, item variance component `2`, and
residual variance component `1`, the absolute errors of persons `0`
and `1` share the same item effect, so their covariance is `2`
(in particular, nonzero), even though every cross-person residual
covariance is `0`. -/
theorem pin_test_shared_item_effects_correlate_people
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (grandMean : ℝ)
    (X : Fin 2 → Fin 1 → Ω → ℝ) (P : Fin 2 → Ω → ℝ)
    (I : Fin 1 → Ω → ℝ) (e : Fin 2 → Fin 1 → Ω → ℝ)
    (hX : ∀ p i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hP_mem : ∀ p, MemLp (P p) 2 μ)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ p i, MemLp (e p i) 2 μ)
    (hP_mean : ∀ p, μ[P p] = 0)
    (hI_mean : ∀ i, μ[I i] = 0)
    (he_mean : ∀ p i, μ[e p i] = 0)
    (hP_cov : ∀ p q, cov[P p, P q; μ]
      = if p = q then (0 : ℝ) else 0)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then (2 : ℝ) else 0)
    (he_cov : ∀ p i q j, cov[e p i, e q j; μ]
      = if (p, i) = (q, j) then (1 : ℝ) else 0)
    (hPI_cov : ∀ p i, cov[P p, I i; μ] = 0)
    (hIP_cov : ∀ i p, cov[I i, P p; μ] = 0)
    (hPe_cov : ∀ p q i, cov[P p, e q i; μ] = 0)
    (heP_cov : ∀ p i q, cov[e p i, P q; μ] = 0)
    (hIe_cov : ∀ i p j, cov[I i, e p j; μ] = 0)
    (heI_cov : ∀ p i j, cov[e p i, I j; μ] = 0) :
    cov[Delta_p grandMean X P 0, Delta_p grandMean X P 1; μ] = 2
      ∧ cov[Delta_p grandMean X P 0, Delta_p grandMean X P 1; μ]
        ≠ 0 := by
  have hD0 : Delta_p grandMean X P 0 = I 0 + e 0 0 := by
    funext ω
    unfold Delta_p
    have h1 : ∀ i : Fin 1, X 0 i ω = grandMean + P 0 ω + I i ω + e 0 i ω := by
      intro i
      rw [hX 0 i]
    simp_rw [h1]
    simp
    ring
  have hD1 : Delta_p grandMean X P 1 = I 0 + e 1 0 := by
    funext ω
    unfold Delta_p
    have h1 : ∀ i : Fin 1, X 1 i ω = grandMean + P 1 ω + I i ω + e 1 i ω := by
      intro i
      rw [hX 1 i]
    simp_rw [h1]
    simp
    ring
  have hI0 : MemLp (I 0) 2 μ := hI_mem 0
  have he00 : MemLp (e 0 0) 2 μ := he_mem 0 0
  have he10 : MemLp (e 1 0) 2 μ := he_mem 1 0
  have hcov : cov[Delta_p grandMean X P 0, Delta_p grandMean X P 1; μ] = 2 := by
    rw [hD0, hD1]
    rw [covariance_add_left hI0 he00 (hI0.add he10)]
    rw [covariance_add_right hI0 hI0 he10]
    rw [covariance_add_right he00 hI0 he10]
    have hII : cov[I 0, I 0; μ] = 2 := by
      have h := hI_cov 0 0
      simp at h
      exact h
    have hIe : cov[I 0, e 1 0; μ] = 0 := hIe_cov 0 1 0
    have heI : cov[e 0 0, I 0; μ] = 0 := heI_cov 0 0 0
    have hee : cov[e 0 0, e 1 0; μ] = 0 := by
      have h := he_cov 0 0 1 0
      simp at h
      exact h
    rw [hII, hIe, heI, hee]
    norm_num
  exact ⟨hcov, by rw [hcov]; norm_num⟩

/-- The public error definitions at two items: the person mean is over
both items, with `m = 2`. -/
theorem test_delta_two_items {Ω : Type*} (X : Fin 1 → Fin 2 → Ω → ℝ)
    (P : Fin 1 → Ω → ℝ) (I : Fin 2 → Ω → ℝ) (ω : Ω) :
    Delta_p (0 : ℝ) X P 0 ω
        = (1 / 2) * (X 0 0 ω + X 0 1 ω) - (0 + P 0 ω)
      ∧ delta_p (0 : ℝ) X P I 0 ω
        = (1 / 2) * (X 0 0 ω + X 0 1 ω)
          - (0 + P 0 ω + (1 / 2) * (I 0 ω + I 1 ω)) := by
  constructor <;> simp [Delta_p, delta_p, Fin.sum_univ_two]


/-- two items with item component 2 and residual component 1.

The absolute error variance is `(2 + 1) / 2 = 3 / 2` and the relative
error variance is `1 / 2`. -/
theorem pin_test_two_items_concrete_variances
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (grandMean : ℝ)
    (X : Fin 1 → Fin 2 → Ω → ℝ) (P : Fin 1 → Ω → ℝ)
    (I : Fin 2 → Ω → ℝ) (e : Fin 1 → Fin 2 → Ω → ℝ)
    (p : Fin 1)
    (hX : ∀ p i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hP_mem : ∀ p, MemLp (P p) 2 μ)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ p i, MemLp (e p i) 2 μ)
    (hP_mean : ∀ p, μ[P p] = 0)
    (hI_mean : ∀ i, μ[I i] = 0)
    (he_mean : ∀ p i, μ[e p i] = 0)
    (hP_cov : ∀ p q, cov[P p, P q; μ]
      = if p = q then (0 : ℝ) else 0)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then (2 : ℝ) else 0)
    (he_cov : ∀ p i q j, cov[e p i, e q j; μ]
      = if (p, i) = (q, j) then (1 : ℝ) else 0)
    (hPI_cov : ∀ p i, cov[P p, I i; μ] = 0)
    (hIP_cov : ∀ i p, cov[I i, P p; μ] = 0)
    (hPe_cov : ∀ p q i, cov[P p, e q i; μ] = 0)
    (heP_cov : ∀ p i q, cov[e p i, P q; μ] = 0)
    (hIe_cov : ∀ i p j, cov[I i, e p j; μ] = 0)
    (heI_cov : ∀ p i j, cov[e p i, I j; μ] = 0) :
    Var[Delta_p grandMean X P p; μ] = 3 / 2
      ∧ Var[delta_p grandMean X P I p; μ] = 1 / 2 := by
  have hm_pos : 0 < (Fintype.card (Fin 2) : ℝ) := by simp
  have hmain := variance_absolute_relative_errors grandMean X P I e 0 2 1 p
    hX hP_mem hI_mem he_mem hP_mean hI_mean he_mean hP_cov hI_cov he_cov
    hPI_cov hIP_cov hPe_cov heP_cov hIe_cov heI_cov
    le_rfl (by norm_num) zero_le_one hm_pos
  simp only [Fintype.card_fin] at hmain
  obtain ⟨hDelta, hdelta⟩ := hmain
  constructor
  · rw [hDelta]
    norm_num
  · rw [hdelta]
    norm_num
end MathlibExtTest.Probability.Statistics.Measurement
