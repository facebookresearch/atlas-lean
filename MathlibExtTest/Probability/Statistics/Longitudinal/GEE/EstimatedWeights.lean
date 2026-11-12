/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.EstimatedWeights
public import MathlibExtTest.Probability.Statistics.Longitudinal.GEE.Sandwich

/-!
# Tests for GEE with estimated working-correlation weights

* **Finite-sample bias (boundary).** On a two-point space with `Y ∈ {0, 2}`, `E[Y] = 1`, and the
  residual-linear weight `L α r = (1 + α²)⁻¹ r`, the fixed weight `L 0` gives an unbiased score
  (`integral_fixed_weight`), but the plug-in `α̂ = Y` gives `E[L α̂ (Y - 1)] = -2 / 5 ≠ 0`
  (`integral_estimated_weight`): unbiasedness with estimated weights holds only asymptotically.
* Smoke tests of `hasFDerivAt_apply_residual` and `integral_nuisanceDeriv_eq_zero` (on the
  two-point space), `tendstoInMeasure_of_sqrt_smul_sub_bounded`, `sqrt_smul_sub_bounded_prodMk`
  and `sqrt_smul_sub_bounded_of_lipschitz_plugin`.
* **Plug-in negligibility.** `tendstoInMeasure_Ualt`: scores `θ (-1)^i` with the plug-in
  `θhat n = (√n)⁻¹` satisfy every hypothesis of
  `tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt`, and the plug-in changes the score
  (`Ualt_plugin_one`). **Boundary**: for scores `θ`, whose nuisance derivative `1` does not
  average to `0`, the plug-in shifts the normalized score by `1` for every `n ≥ 1`
  (`not_tendstoInMeasure_of_nuisanceDeriv_ne_zero`), so that hypothesis cannot be dropped.
* **The random-intercept model of the `Sandwich` tests with an estimated exchangeable working
  correlation.** The GEE score is `(1 + α)⁻¹ ((Y 1 - β) + (Y 2 - β))` (`Uex`), and the
  data-dependent plug-in `α̂ n = (√n)⁻¹ sin (n⁻¹ ∑ ⟪ξ i, s⟫)` (`αhat`) uses every cluster. Every
  hypothesis is discharged for
  - `tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights`
    (`tendstoInDistribution_exchangeable_estimated`), including the uniform negligibility of the
    averaged nuisance derivative from the law of large numbers;
  - `tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt`, hence
    `linearization_estimatedWeights_of_hasFDerivAt`
    (`tendstoInDistribution_exchangeable_estimated_of_hasFDerivAt`);
  - `tendstoInMeasure_empirical_sandwichCovariance_estimatedWeights`
    (`tendstoInMeasure_empirical_sandwich_exchangeable`), with limit `3 / 2`.

  The limit is the sandwich `3 / 2` of the fixed-weight model. With equal cluster sizes and an
  intercept-only mean, the exchangeable weight is scalar, so the root (the grand mean) does not
  depend on `α̂`; the scores, the nuisance derivatives, the linearization remainder
  (`lin_remainder`) and the plug-in bread and meat do. The plug-in `αhat` is a stand-in with
  `√n αhat` bounded by `1`, not the moment estimator of `α`. The model is realized on an
  infinite product space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.GEE Filter Finset RealInnerProductSpace
open scoped Real Topology ENNReal

namespace GEEEstimatedWeightsTest

/-! ### Finite-sample bias of the estimated-weight score -/

/-- A two-point sample space, each point with probability `1 / 2`. -/
noncomputable def Pb : Measure Bool := (1 / 2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsFiniteMeasure Pb :=
  ⟨by simp [Pb]⟩

/-- A single response with values `2` and `0`, so `E[Y] = 1`. -/
def Yb : Bool → ℝ := fun b ↦ if b then 2 else 0

/-- The residual-linear weight `L α r = (1 + α²)⁻¹ r` of a scalar working variance `1 + α²`. -/
noncomputable def Lb (α : ℝ) : ℝ →L[ℝ] ℝ := (1 + α ^ 2)⁻¹ • 1

theorem integral_Pb (f : Bool → ℝ) : ∫ ω, f ω ∂Pb = (f true + f false) / 2 := by
  rw [Pb, integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite), integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The mean model `E[Y] = 1` is correct. -/
theorem integral_Yb_sub_one : ∫ ω, (Yb ω - 1) ∂Pb = 0 := by
  rw [integral_Pb]
  norm_num [Yb]

/-- With the weight fixed at `α = 0`, the score `L 0 (Y - 1)` is unbiased. -/
theorem integral_fixed_weight : ∫ ω, Lb 0 (Yb ω - 1) ∂Pb = 0 := by
  rw [integral_Pb]
  norm_num [Lb, Yb]

/-- **The estimated-weight score is biased in finite samples.** With the working parameter
estimated from the response, `α̂ = Y`, the score `L α̂ (Y - 1)` has mean `-2 / 5 ≠ 0`, although
the mean model is correct: `E[U(β₀; α̂(Y))] = 0` fails, which is why Liang and Zeger recover
unbiasedness only asymptotically. -/
theorem integral_estimated_weight : ∫ ω, Lb (Yb ω) (Yb ω - 1) ∂Pb = -2 / 5 := by
  rw [integral_Pb]
  norm_num [Lb, Yb]

theorem integral_estimated_weight_ne_zero : ∫ ω, Lb (Yb ω) (Yb ω - 1) ∂Pb ≠ 0 := by
  rw [integral_estimated_weight]
  norm_num

/-! ### The nuisance derivative of a residual-linear score -/

/-- `hasFDerivAt_apply_residual` for the linear weight `L α = α • 1`. -/
example (θ r : ℝ) : HasFDerivAt (fun a : ℝ ↦ (a • (1 : ℝ →L[ℝ] ℝ)) r)
    ((ContinuousLinearMap.apply ℝ ℝ r).comp
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)))) θ :=
  hasFDerivAt_apply_residual ((hasDerivAt_id θ).smul_const (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt r

/-- `integral_nuisanceDeriv_eq_zero` on the two-point model: a nuisance derivative applied to the
mean-zero residual `Y - 1` has mean zero. -/
example (h : ℝ) : ∫ ω, (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)) h
    (Yb ω - 1) ∂Pb = 0 :=
  integral_nuisanceDeriv_eq_zero _ Integrable.of_finite integral_Yb_sub_one h

/-! ### `√n`-consistent nuisance estimators -/

/-- The deterministic estimator `θhat n = (n + 1)⁻¹` is `√n`-consistent for `0` (`K = 1`), hence
consistent. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    TendstoInMeasure P (fun (n : ℕ) (_ : Ω) ↦ ((n : ℝ) + 1)⁻¹) atTop (fun _ ↦ 0) := by
  refine tendstoInMeasure_of_sqrt_smul_sub_bounded fun ε _ ↦ ⟨1, fun n ↦ ?_⟩
  refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).le.trans zero_le
  simp only [Set.mem_ofPred_eq, sub_zero, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_inv] at hω
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_of_pos hn] at hω
  have hs : √(n : ℝ) ≤ n + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  exact absurd hω (not_lt.2 ((mul_inv_le_iff₀ hn).2 (by linarith)))

/-- `sqrt_smul_sub_bounded_prodMk` and `sqrt_smul_sub_bounded_of_lipschitz_plugin` on
deterministic sequences: `φhat n = (√n)⁻¹`, and `αhat n = 3 φhat n`, a plug-in of `φhat` with
Lipschitz factor `H = 3` and an exact oracle `α̃ = 0`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {_ω : Ω | K < ‖√(n : ℝ) • (((3 : ℝ) * (√(n : ℝ))⁻¹, (√(n : ℝ))⁻¹) - ((0 : ℝ), (0 : ℝ)))‖}
        ≤ ε := by
  have hφ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω : Ω | K < ‖√(n : ℝ) • ((√(n : ℝ))⁻¹ - (0 : ℝ))‖} ≤ ε := by
    refine fun ε _ ↦ ⟨1, fun n ↦ ?_⟩
    refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).le.trans zero_le
    simp only [Set.mem_ofPred_eq, sub_zero, smul_eq_mul] at hω
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · simp [h] at hω
      exact absurd hω (by norm_num)
    · rw [mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg n) h.symm)),
        norm_one] at hω
      exact absurd hω (lt_irrefl 1)
  refine sqrt_smul_sub_bounded_prodMk ?_ hφ
  refine sqrt_smul_sub_bounded_of_lipschitz_plugin (atilde := fun _ _ ↦ 0) (H := fun _ _ ↦ 3)
    (fun n ω ↦ ?_) (fun ε _ ↦ ⟨3, fun n ↦ by simp⟩) hφ (fun ε _ ↦ ⟨0, fun n ↦ by simp⟩)
  simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ### Plug-in negligibility: a positive instance and the boundary case -/

/-- `|∑_{i<n} (-1)^i| ≤ 1`. -/
theorem abs_sum_neg_one_pow_le (n : ℕ) : |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ 1 := by
  rw [geom_sum_eq (by norm_num : (-1 : ℝ) ≠ 1)]
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num

theorem hasFDerivAt_mul_const (c θ : ℝ) :
    HasFDerivAt (fun a : ℝ ↦ a * c) (c • (1 : ℝ →L[ℝ] ℝ)) θ :=
  (c • (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt.congr_of_eventuallyEq
    (Eventually.of_forall fun a ↦ by simp [mul_comm])

theorem norm_smul_one (c : ℝ) : ‖c • (1 : ℝ →L[ℝ] ℝ)‖ = |c| := by
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs]

theorem sqrt_smul_inv_sqrt_le (n : ℕ) : ‖√(n : ℝ) • ((√(n : ℝ))⁻¹ - (0 : ℝ))‖ ≤ 1 := by
  rw [sub_zero, smul_eq_mul]
  rcases eq_or_ne (n : ℝ) 0 with h | h
  · simp [h]
  · rw [mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg n) h.symm)),
      norm_one]

/-- Alternating cluster scores `U i β θ = θ (-1)^i`. -/
def Ualt {Ω : Type*} (i : ℕ) (_β θ : ℝ) (_ω : Ω) : ℝ := θ * (-1 : ℝ) ^ i

/-- The plug-in `θhat n = (√n)⁻¹`. -/
noncomputable def θalt {Ω : Type*} (n : ℕ) (_ω : Ω) : ℝ := (√(n : ℝ))⁻¹

/-- **Plug-in negligibility, positive instance.** Cluster scores `U i β θ = θ (-1)^i` with
nuisance derivative `(-1)^i`, whose average tends to `0`, and the plug-in `θhat n = (√n)⁻¹`
(`√n θhat n = 1`, bounded). Every hypothesis of
`tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt` holds, and the normalized score with
the plug-in differs from the one at `θ₀ = 0` by `(√n)⁻¹ θhat n ∑_{i<n} (-1)^i → 0`; at `n = 1`
the difference is `1 ≠ 0` (`Ualt_plugin_one`), so the plug-in genuinely changes the score. -/
theorem tendstoInMeasure_Ualt {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) ↦
      (√n)⁻¹ • ∑ i ∈ range n, Ualt i 0 (θalt n ω) ω - (√n)⁻¹ • ∑ i ∈ range n, Ualt i 0 0 ω)
      atTop 0 := by
  refine tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt (E := ℝ) (F := ℝ)
    (DθU := fun i _ _ ↦ ((-1 : ℝ) ^ i) • (1 : ℝ →L[ℝ] ℝ)) one_pos
    (fun i ω θ _ ↦ hasFDerivAt_mul_const _ θ) (fun ε hε ↦ ?_)
    (fun ε _ ↦ ⟨1, fun n ↦ ?_⟩)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈ε⁻¹⌉₊] with n hn
    refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).symm
    obtain ⟨θ, _, hθ⟩ := hω
    rw [← Finset.sum_smul, smul_smul, norm_smul_one, abs_mul, abs_inv, Nat.abs_cast] at hθ
    have hn' : ε⁻¹ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    have hnpos : (0 : ℝ) < n := (inv_pos.2 hε).trans hn'
    have h1 : (n : ℝ)⁻¹ * |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ (n : ℝ)⁻¹ :=
      mul_le_of_le_one_right (inv_nonneg.2 hnpos.le) (abs_sum_neg_one_pow_le n)
    have h2 : (n : ℝ)⁻¹ < ε := by
      rw [inv_lt_comm₀ hnpos hε]
      exact hn'
    exact absurd hθ (not_le.2 (h1.trans_lt h2))
  · refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).le.trans zero_le
    exact absurd hω (not_lt.2 (sqrt_smul_inv_sqrt_le n))

theorem Ualt_plugin_one {Ω : Type*} (ω : Ω) :
    (√(1 : ℕ))⁻¹ • ∑ i ∈ range 1, Ualt i 0 (θalt 1 ω) ω -
      (√(1 : ℕ))⁻¹ • ∑ i ∈ range 1, Ualt i (0 : ℝ) 0 ω = 1 := by
  simp [Ualt, θalt]

/-- **Boundary: a non-vanishing nuisance derivative breaks plug-in negligibility.** With cluster
scores `U i β θ = θ`, the nuisance derivative is `1` for every cluster, so its average does not
tend to `0` (the hypothesis that `integral_nuisanceDeriv_eq_zero` supplies for residual-linear
scores fails); all other hypotheses of `tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt`
hold with `θhat n = (√n)⁻¹`. The plug-in shifts the normalized score by exactly `1` for every
`n ≥ 1`, so the conclusion fails. -/
theorem not_tendstoInMeasure_of_nuisanceDeriv_ne_zero :
    ¬ TendstoInMeasure (Measure.dirac ()) (fun (n : ℕ) (_ : Unit) ↦
      (√n)⁻¹ • ∑ _i ∈ range n, (√(n : ℝ))⁻¹ - (√n)⁻¹ • ∑ _i ∈ range n, (0 : ℝ)) atTop 0 := by
  intro h
  rw [tendstoInMeasure_iff_norm] at h
  have h1 := h (1 / 2) (by norm_num)
  have h2 : ∀ᶠ n : ℕ in atTop, Measure.dirac () {ω : Unit | 1 / 2 ≤
      ‖(fun (n : ℕ) (_ : Unit) ↦ (√n)⁻¹ • ∑ _i ∈ range n, (√(n : ℝ))⁻¹ -
        (√n)⁻¹ • ∑ _i ∈ range n, (0 : ℝ)) n ω - (0 : Unit → ℝ) ω‖} = 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hval : (√(n : ℝ))⁻¹ • ∑ _i ∈ range n, (√(n : ℝ))⁻¹ -
        (√(n : ℝ))⁻¹ • ∑ _i ∈ range n, (0 : ℝ) = 1 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul, mul_zero,
        sub_zero]
      have hs := Real.mul_self_sqrt hn'.le
      have hs0 : √(n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hn'
      field_simp
      linarith
    have huniv : {ω : Unit | 1 / 2 ≤ ‖(fun (n : ℕ) (_ : Unit) ↦
        (√n)⁻¹ • ∑ _i ∈ range n, (√(n : ℝ))⁻¹ - (√n)⁻¹ • ∑ _i ∈ range n, (0 : ℝ)) n ω -
        (0 : Unit → ℝ) ω‖} = Set.univ := by
      ext ω
      simp only [Pi.zero_apply, sub_zero, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [hval, norm_one]
      norm_num
    rw [huniv, measure_univ]
  have h3 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun _ h ↦ h.symm))
  exact zero_ne_one h3

/-! ### The random-intercept model with an estimated exchangeable working correlation -/

section RandomIntercept

open GEESandwichTest

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → GEESandwichTest.F}

/-- The GEE score of cluster `i` in the random-intercept model of the `Sandwich` tests under the
exchangeable working correlation `R(α) = [[1, α], [α, 1]]`: since
`(1, 1) R(α)⁻¹ = (1 + α)⁻¹ (1, 1)`, `Dᵀ R(α)⁻¹ (Y - μ(β)) = (1 + α)⁻¹ ((Y 1 - β) + (Y 2 - β))`. -/
noncomputable def Uex (β₀ : ℝ) (ξ : ℕ → Ω → GEESandwichTest.F) (i : ℕ) (β α : ℝ) (ω : Ω) : ℝ :=
  (1 + α)⁻¹ * U β₀ ξ i β ω

/-- A data-dependent working-correlation estimate `α̂ n = (√n)⁻¹ sin (n⁻¹ ∑_{i<n} ⟪ξ i, s⟫)`; it
depends on the responses of every cluster, and `√n α̂ n` is bounded by `1`. It is not the moment
estimator of `α`, whose `√n`-consistency would need a separate CLT. -/
noncomputable def αhat (ξ : ℕ → Ω → GEESandwichTest.F) (n : ℕ) (ω : Ω) : ℝ :=
  (√(n : ℝ))⁻¹ * Real.sin (m1 ξ n ω)

/-- The nuisance derivative of `Uex` at `α`: `-(1 + α)⁻² U`. -/
noncomputable def DαUex (β₀ : ℝ) (ξ : ℕ → Ω → GEESandwichTest.F) (i : ℕ) (α : ℝ) (ω : Ω) :
    ℝ →L[ℝ] ℝ :=
  (-1 / (1 + α) ^ 2 * U β₀ ξ i β₀ ω) • 1

theorem Uex_zero (β₀ : ℝ) (k : ℕ) : Uex β₀ ξ k β₀ 0 = U β₀ ξ k β₀ := by
  ext ω
  simp [Uex]

theorem abs_αhat_le (n : ℕ) (ω : Ω) : |αhat ξ n ω| ≤ (√(n : ℝ))⁻¹ := by
  rw [αhat, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.abs_sin_le_one _)

theorem norm_sqrt_smul_αhat_le (n : ℕ) (ω : Ω) : ‖√(n : ℝ) • (αhat ξ n ω - 0)‖ ≤ 1 := by
  rw [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_ne (n : ℝ) 0 with h | h
  · simp [h]
  · have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (lt_of_le_of_ne (Nat.cast_nonneg n) h.symm)
    calc √(n : ℝ) * |αhat ξ n ω| ≤ √(n : ℝ) * (√(n : ℝ))⁻¹ := by
          gcongr
          exact abs_αhat_le n ω
      _ = 1 := mul_inv_cancel₀ hs.ne'

theorem hasFDerivAt_Uex (β₀ : ℝ) (i : ℕ) (ω : Ω) {α : ℝ} (hα : α ∈ Metric.ball (0 : ℝ) (1 / 2)) :
    HasFDerivAt (fun a ↦ Uex β₀ ξ i β₀ a ω) (DαUex β₀ ξ i α ω) α := by
  have hα' : |α| < 1 / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hα
  have hne : 1 + α ≠ 0 := by
    intro h
    rw [abs_lt] at hα'
    linarith
  have h := ((((hasDerivAt_id α).const_add 1).inv (by simpa using hne)).mul_const
    (U β₀ ξ i β₀ ω)).hasFDerivAt
  refine h.congr_fderiv ?_
  ext
  simp [DαUex]

theorem norm_avg_DαUex (β₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (ω : Ω) :
    ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DαUex β₀ ξ i α ω‖ = |1 / (1 + α) ^ 2| * |m1 ξ n ω| := by
  have havg := avg_U β₀ ξ hn β₀ ω
  rw [sub_self, mul_zero, add_zero, smul_eq_mul] at havg
  simp only [DαUex, ← Finset.sum_smul, smul_smul, norm_smul, norm_one, mul_one,
    ← Finset.mul_sum, Real.norm_eq_abs]
  rw [show (n : ℝ)⁻¹ * (-1 / (1 + α) ^ 2 * ∑ i ∈ range n, U β₀ ξ i β₀ ω) =
    -1 / (1 + α) ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ range n, U β₀ ξ i β₀ ω) by ring, havg, abs_mul,
    neg_div, abs_neg]

theorem measurable_m1 (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) : Measurable (m1 ξ n) :=
  (Finset.measurable_sum _ fun i _ ↦ measurable_inner_s.comp (hξ i)).div_const _

theorem sum_Uex (β₀ : ℝ) (n : ℕ) (β α : ℝ) (ω : Ω) :
    ∑ i ∈ range n, Uex β₀ ξ i β α ω = (1 + α)⁻¹ * ∑ i ∈ range n, U β₀ ξ i β ω := by
  simp only [Uex, Finset.mul_sum]

/-- The grand mean is the root of the estimated-weight equation, for every `n`. -/
theorem sum_Uex_βhat (β₀ : ℝ) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, Uex β₀ ξ i (βhat β₀ ξ n ω) (αhat ξ n ω) ω = 0 := by
  rw [sum_Uex, sum_U_βhat, mul_zero]

/-- The linearization remainder of the estimated-weight equation:
`n⁻¹ (∑ U(βhat, α̂) - ∑ U(β₀, α̂)) - A (βhat - β₀) = 2 (1 - (1 + α̂)⁻¹) (βhat - β₀)`. -/
theorem lin_remainder (β₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) :
    (n : ℝ)⁻¹ • (∑ i ∈ range n, Uex β₀ ξ i (βhat β₀ ξ n ω) (αhat ξ n ω) ω -
      ∑ i ∈ range n, Uex β₀ ξ i β₀ (αhat ξ n ω) ω) - A (βhat β₀ ξ n ω - β₀) =
      2 * (1 - (1 + αhat ξ n ω)⁻¹) * (βhat β₀ ξ n ω - β₀) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  rw [sum_Uex, sum_Uex, sum_U, sum_U]
  simp only [A, smul_apply, one_apply_eq_self, smul_eq_mul]
  field_simp
  ring

/-- **The random-intercept model with an estimated exchangeable working correlation satisfies
every hypothesis of `tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights`.** The
estimated-weight root (the grand mean, `sum_Uex_βhat`) is asymptotically `N(0, 3/2)`, the
sandwich of the model at the limiting working correlation `α₀ = 0`, with the data-dependent
plug-in `α̂` of `αhat`. For this intercept-only model with equal cluster sizes the
exchangeable weight is a scalar multiple of the identity, so the root itself does not depend on
`α̂`; the estimated-weight scores, their nuisance derivatives and the linearization remainder
do (`lin_remainder`). -/
theorem tendstoInDistribution_exchangeable_estimated (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian GEESandwichTest.F) P) (hind : iIndepFun ξ P)
    (β₀ : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat β₀ ξ n ω - β₀)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (3 / 2)) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hαmeas : ∀ n, Measurable (αhat ξ n) := fun n ↦
    measurable_const.mul (Real.measurable_sin.comp (measurable_m1 hξ n))
  have hUmeas : ∀ i, Measurable (U β₀ ξ i β₀) := fun i ↦ by
    rw [U_self]
    exact measurable_inner_s.comp (hξ i)
  refine tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights (E := ℝ) (F := ℝ)
    (U := Uex β₀ ξ) (DθU := DαUex β₀ ξ) (θ₀ := 0) (A := A) (B := B) (by norm_num : (0 : ℝ) < 1 / 2)
    isUnit_A (fun k ↦ by rw [Uex_zero]; exact hUmeas k)
    (by simp_rw [Uex_zero, U_self]; exact hind.comp (fun _ x ↦ ⟪x, s⟫) fun _ ↦ measurable_inner_s)
    (fun k ↦ by rw [Uex_zero, U_self]; exact integral_inner_s hlaw k)
    (fun k ↦ by rw [Uex_zero]; exact memLp_U hlaw β₀ k)
    (by simp_rw [Uex_zero]; exact tendsto_meat hlaw β₀)
    (fun t ↦ by
      simp_rw [Uex_zero]
      exact lindebergConditionTriangular_inner_of_identDistrib (identDistrib_U hlaw β₀)
        (memLp_U hlaw β₀ 0) t)
    (fun i ω α hα ↦ hasFDerivAt_Uex β₀ i ω hα) (fun ε hε ↦ ?_)
    (fun ε _ ↦ ⟨1, fun n ↦ (measure_mono_null (t := ∅)
      (fun ω hω ↦ absurd hω (not_lt.2 (norm_sqrt_smul_αhat_le n ω))) measure_empty).le.trans
        zero_le⟩)
    (fun n ↦ (Finset.measurable_sum _ fun i _ ↦
      ((measurable_const.add (hαmeas n)).inv).mul (hUmeas i)).aemeasurable)
    (fun n ↦ (measurable_βhat hξ β₀ n).aemeasurable) (by simp [sum_Uex_βhat]) (fun ε hε ↦ ?_)
    aemeasurable_id hasLaw_limit
  · -- the averaged nuisance derivative tends to `0` uniformly near `α₀ = 0`
    have hm1 := tendstoInMeasure_m1 hξ hlaw hind
    rw [tendstoInMeasure_iff_norm] at hm1
    refine tendsto_measure_of_eventually_subset (hm1 (ε / 4) (by positivity)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω hω
    obtain ⟨α, hα, hle⟩ := hω
    have hα' : |α| < 1 / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hα
    rw [abs_lt] at hα'
    rw [norm_avg_DαUex β₀ hn] at hle
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs]
    have hpos : 0 < (1 + α) ^ 2 := by nlinarith
    have hq : |1 / (1 + α) ^ 2| ≤ 4 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ hpos]
      nlinarith
    nlinarith [abs_nonneg (m1 ξ n ω)]
  · -- the linearization remainder is eventually below `ε ‖βhat - β₀‖`
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1, hsqrt.eventually_gt_atTop (max 2 (4 / ε))] with n hn hs
    refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).symm
    simp only [Set.mem_ofPred_eq] at hω
    rw [lin_remainder β₀ hn ω, norm_mul, norm_mul] at hω
    have hs2 : 2 < √(n : ℝ) := (le_max_left _ _).trans_lt hs
    have hsε : 4 / ε < √(n : ℝ) := (le_max_right _ _).trans_lt hs
    have hspos : 0 < √(n : ℝ) := by linarith
    have ha := abs_αhat_le (ξ := ξ) n ω
    set a := αhat ξ n ω
    have hainv : (√(n : ℝ))⁻¹ < 1 / 2 := by
      rw [inv_lt_comm₀ hspos (by norm_num)]
      linarith
    have ha2 : |a| < 1 / 2 := ha.trans_lt hainv
    rw [abs_lt] at ha2
    have h1a : 0 < 1 + a := by linarith
    have hfac : ‖(2 : ℝ)‖ * ‖1 - (1 + a)⁻¹‖ ≤ ε := by
      have heq : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
      rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos h1a, abs_two]
      have h4 : 4 * (√(n : ℝ))⁻¹ ≤ ε := by
        rw [div_lt_iff₀ hε] at hsε
        rw [← div_eq_mul_inv, div_le_iff₀ hspos]
        linarith
      calc 2 * (|a| / (1 + a)) ≤ 2 * (|a| / (1 / 2)) := by
            gcongr
            linarith
        _ = 4 * |a| := by ring
        _ ≤ 4 * (√(n : ℝ))⁻¹ := by gcongr
        _ ≤ ε := h4
    exact absurd hω (not_lt.2 (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)))

/-- The `β`-Jacobian of the estimated-weight score: `(1 + α)⁻¹ A`. -/
theorem hasFDerivAt_Uex_β (β₀ : ℝ) (i : ℕ) (ω : Ω) (α b : ℝ) :
    HasFDerivAt (fun β ↦ Uex β₀ ξ i β α ω) ((1 + α)⁻¹ • A) b :=
  (hasFDerivAt_U β₀ ξ i ω b).const_smul (1 + α)⁻¹

/-- The sensitivity at nuisance value `α`: `Abar (β, α) = (1 + α)⁻¹ A`. -/
noncomputable def Abarex (p : ℝ × ℝ) : ℝ →L[ℝ] ℝ := (1 + p.2)⁻¹ • A

/-- The meat limit at `(β, α)`: `Bbar (β, α) = (1 + α)⁻² Bbar β`. -/
noncomputable def Bbarex (β₀ : ℝ) (p : ℝ × ℝ) : ℝ →L[ℝ] ℝ :=
  ((1 + p.2) ^ 2)⁻¹ • GEESandwichTest.Bbar β₀ p.1

theorem Abarex_zero (β₀ : ℝ) : Abarex (β₀, 0) = A := by simp [Abarex]

theorem Bbarex_zero (β₀ : ℝ) : Bbarex β₀ (β₀, 0) = B := by
  simp [Bbarex, GEESandwichTest.Bbar, B]

theorem continuousAt_Abarex (β₀ : ℝ) : ContinuousAt Abarex (β₀, 0) :=
  ((continuous_const.add continuous_snd).continuousAt.inv₀ (by norm_num)).smul continuousAt_const

theorem continuousAt_Bbarex (β₀ : ℝ) : ContinuousAt (Bbarex β₀) (β₀, 0) := by
  have hB : Continuous (GEESandwichTest.Bbar β₀) := by unfold GEESandwichTest.Bbar; fun_prop
  exact (((continuous_const.add continuous_snd).pow 2).continuousAt.inv₀ (by norm_num)).smul
    (hB.comp continuous_fst).continuousAt

omit [IsProbabilityMeasure P] in
/-- The averaged estimated-weight Jacobian equals `Abarex` exactly for `n ≥ 1`. -/
theorem tendsto_jacobian_ex (β₀ δ : ℝ) :
    ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {_ω | ∃ p ∈ Metric.ball ((β₀, 0) : ℝ × ℝ) δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ _i ∈ range n, (1 + p.2)⁻¹ • A - Abarex p‖}) atTop (𝓝 0) := by
  intro ε hε
  refine tendsto_measure_of_eventually_subset (T := fun _ ↦ ∅) (by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn _ω hω
  obtain ⟨p, -, hp⟩ := hω
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul, Abarex, sub_self, norm_zero] at hp
  exact absurd hp (not_le.2 hε)

theorem avg_rankOne_Uex (β₀ : ℝ) (n : ℕ) (β α : ℝ) (ω : Ω) :
    (n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (Uex β₀ ξ i β α ω)
      (Uex β₀ ξ i β α ω) = ((1 + α) ^ 2)⁻¹ •
      ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U β₀ ξ i β ω) (U β₀ ξ i β ω)) := by
  simp only [rankOne_real, ← Finset.sum_smul, smul_smul]
  congr 1
  simp only [Uex, mul_pow, ← Finset.mul_sum, inv_pow]
  ring

/-- **The combined estimated-weights theorem in the model**:
`tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt`, hence
`linearization_estimatedWeights_of_hasFDerivAt`, with the `β`-Jacobian `(1 + α)⁻¹ A`, the
sensitivity `Abarex`, and consistency of the grand mean. -/
theorem tendstoInDistribution_exchangeable_estimated_of_hasFDerivAt (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian GEESandwichTest.F) P) (hind : iIndepFun ξ P)
    (β₀ : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat β₀ ξ n ω - β₀)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (3 / 2)) := by
  have hαmeas : ∀ n, Measurable (αhat ξ n) := fun n ↦
    measurable_const.mul (Real.measurable_sin.comp (measurable_m1 hξ n))
  have hUmeas : ∀ i, Measurable (U β₀ ξ i β₀) := fun i ↦ by
    rw [U_self]
    exact measurable_inner_s.comp (hξ i)
  have hm1 := tendstoInMeasure_m1 hξ hlaw hind
  rw [tendstoInMeasure_iff_norm] at hm1
  refine tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt
    (E := ℝ) (F := ℝ) (U := Uex β₀ ξ) (DU := fun _ _ α _ ↦ (1 + α)⁻¹ • A)
    (DθU := DαUex β₀ ξ) (θ₀ := 0) (Abar := Abarex) (B := B) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun i ω α _ β _ ↦ hasFDerivAt_Uex_β β₀ i ω α β) (continuousAt_Abarex β₀)
    (by rw [Abarex_zero]; exact isUnit_A) (tendsto_jacobian_ex β₀ (1 / 2))
    (fun i ω α hα ↦ hasFDerivAt_Uex β₀ i ω hα) (fun ε hε ↦ ?_)
    (fun ε _ ↦ ⟨1, fun n ↦ (measure_mono_null (t := ∅)
      (fun ω hω ↦ absurd hω (not_lt.2 (norm_sqrt_smul_αhat_le n ω))) measure_empty).le.trans
        zero_le⟩)
    (fun n ↦ (Finset.measurable_sum _ fun i _ ↦
      ((measurable_const.add (hαmeas n)).inv).mul (hUmeas i)).aemeasurable)
    (fun k ↦ by rw [Uex_zero]; exact hUmeas k)
    (by simp_rw [Uex_zero, U_self]; exact hind.comp (fun _ x ↦ ⟪x, s⟫) fun _ ↦ measurable_inner_s)
    (fun k ↦ by rw [Uex_zero, U_self]; exact integral_inner_s hlaw k)
    (fun k ↦ by rw [Uex_zero]; exact memLp_U hlaw β₀ k)
    (by simp_rw [Uex_zero]; exact tendsto_meat hlaw β₀)
    (fun t ↦ by
      simp_rw [Uex_zero]
      exact lindebergConditionTriangular_inner_of_identDistrib (identDistrib_U hlaw β₀)
        (memLp_U hlaw β₀ 0) t)
    (fun n ↦ (measurable_βhat hξ β₀ n).aemeasurable) (tendstoInMeasure_βhat hξ hlaw hind β₀)
    (by simp [sum_Uex_βhat]) aemeasurable_id (by rw [Abarex_zero]; exact hasLaw_limit)
  refine tendsto_measure_of_eventually_subset (hm1 (ε / 4) (by positivity)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω hω
  obtain ⟨α, hα, hle⟩ := hω
  have hα' : |α| < 1 / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hα
  rw [abs_lt] at hα'
  rw [norm_avg_DαUex β₀ hn] at hle
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs]
  have hpos : 0 < (1 + α) ^ 2 := by nlinarith
  have hq : |1 / (1 + α) ^ 2| ≤ 4 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ hpos]
    nlinarith
  nlinarith [abs_nonneg (m1 ξ n ω)]

/-- **The empirical sandwich with estimated weights is consistent in the model**, from
`tendstoInMeasure_empirical_sandwichCovariance_estimatedWeights`: plug-in bread
`n⁻¹ ∑ (1 + α̂)⁻¹ A` and meat `n⁻¹ ∑ Uex(βhat, α̂)²` converge in probability to the sandwich
`3 / 2` of the model at `α₀ = 0`. -/
theorem tendstoInMeasure_empirical_sandwich_exchangeable (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian GEESandwichTest.F) P) (hind : iIndepFun ξ P)
    (β₀ : ℝ) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ _i ∈ range n, (1 + αhat ξ n ω)⁻¹ • A)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n,
          InnerProductSpace.rankOne ℝ (Uex β₀ ξ i (βhat β₀ ξ n ω) (αhat ξ n ω) ω)
            (Uex β₀ ξ i (βhat β₀ ξ n ω) (αhat ξ n ω) ω))) atTop
      (fun _ ↦ (3 / 2 : ℝ) • 1) := by
  have hm1 := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_m1 hξ hlaw hind)
  have hm2 := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_m2 hξ hlaw hind)
  have h := tendstoInMeasure_empirical_sandwichCovariance_estimatedWeights (E := ℝ) (F := ℝ)
    (U := Uex β₀ ξ) (DU := fun _ _ α _ ↦ (1 + α)⁻¹ • A) (θ₀ := 0) (θhat := αhat ξ)
    (Abar := Abarex) (Bbar := Bbarex β₀) (by norm_num : (0 : ℝ) < 1 / 2)
    (continuousAt_Abarex β₀) (continuousAt_Bbarex β₀) (by rw [Abarex_zero]; exact isUnit_A)
    (tendsto_jacobian_ex β₀ (1 / 2)) (fun ε hε ↦ ?_) (tendstoInMeasure_βhat hξ hlaw hind β₀)
    (tendstoInMeasure_of_sqrt_smul_sub_bounded fun ε _ ↦ ⟨1, fun n ↦ (measure_mono_null
      (t := ∅) (fun ω hω ↦ absurd hω (not_lt.2 (norm_sqrt_smul_αhat_le (ξ := ξ) n ω)))
        measure_empty).le.trans zero_le⟩)
  · rwa [Abarex_zero, Bbarex_zero, sandwichCovariance_A_B] at h
  have hsum := (hm2 (ε / 8) (by positivity)).add (hm1 (ε / 32) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  obtain ⟨p, hp, hle⟩ := hω
  obtain ⟨β, α⟩ := p
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
  obtain ⟨hβ, hα⟩ := hp
  rw [sub_zero, abs_lt] at hα
  rw [avg_rankOne_Uex, avg_rankOne β₀ ξ hn, Bbarex, GEESandwichTest.Bbar, smul_smul,
    smul_smul, ← sub_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs] at hle
  have hpos : 0 < (1 + α) ^ 2 := by nlinarith
  have hq : ((1 + α) ^ 2)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    nlinarith
  have hc : |2 * (β₀ - β)| ≤ 2 := by
    rw [abs_mul, abs_two, abs_sub_comm]
    linarith
  simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
  by_contra hcon
  push Not at hcon
  have h3 : |2 * (2 * (β₀ - β)) * m1 ξ n ω| ≤ 4 * |m1 ξ n ω| := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (m1 ξ n ω)]
  have h4 := abs_add_le (m2 ξ n ω - 6) (2 * (2 * (β₀ - β)) * m1 ξ n ω)
  have h5 : ((1 + α) ^ 2)⁻¹ * (m2 ξ n ω + 2 * (2 * (β₀ - β)) * m1 ξ n ω + (2 * (β₀ - β)) ^ 2) -
      ((1 + α) ^ 2)⁻¹ * (6 + (2 * (β₀ - β)) ^ 2) =
      ((1 + α) ^ 2)⁻¹ * (m2 ξ n ω - 6 + 2 * (2 * (β₀ - β)) * m1 ξ n ω) := by ring
  rw [h5, abs_mul, abs_of_pos (inv_pos.2 hpos)] at hle
  have h6 : |m2 ξ n ω - 6 + 2 * (2 * (β₀ - β)) * m1 ξ n ω| < ε / 4 := by
    linarith [hcon.1, hcon.2]
  nlinarith [abs_nonneg (m2 ξ n ω - 6 + 2 * (2 * (β₀ - β)) * m1 ξ n ω)]

/-- The model with the estimated exchangeable correlation is realized by i.i.d. standard Gaussian
vectors on the infinite product space, so the hypotheses above are jointly satisfiable. -/
example (β₀ : ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ ↦ stdGaussian GEESandwichTest.F)
      (fun (n : ℕ) (ω : ℕ → GEESandwichTest.F) ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ _i ∈ range n, (1 + αhat (fun i ω ↦ ω i) n ω)⁻¹ • A)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ
          (Uex β₀ (fun i ω ↦ ω i) i (βhat β₀ (fun i ω ↦ ω i) n ω) (αhat (fun i ω ↦ ω i) n ω) ω)
          (Uex β₀ (fun i ω ↦ ω i) i (βhat β₀ (fun i ω ↦ ω i) n ω)
            (αhat (fun i ω ↦ ω i) n ω) ω))) atTop
      (fun _ ↦ (3 / 2 : ℝ) • 1) :=
  tendstoInMeasure_empirical_sandwich_exchangeable (fun i ↦ measurable_pi_apply i)
    (fun i ↦ (measurePreserving_eval_infinitePi (fun _ ↦ stdGaussian GEESandwichTest.F) i).hasLaw)
    (iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id) β₀

end RandomIntercept

end GEEEstimatedWeightsTest
