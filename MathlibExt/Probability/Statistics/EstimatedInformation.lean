/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Estimated information in regular likelihood inference

`VectorInference` proves the Wald and score tests for a finite-dimensional parameter with the
**null** Fisher information `I(θ₀)`, and Wilks' theorem for the likelihood ratio at a
consistent root `θhat n` of the likelihood equation. In practice `I(θ₀)` is replaced by an
estimate: the expected information at the estimate, `I(θhat n)`, or the **observed
information** `Ĵₙ(θ) = -(1/n) ∑_{i<n} D_θ score p θ (X i)`. This file supplies those
plug-in versions.

* Observed information is consistent at `θ₀` by the strong law of large numbers. It is also
  consistent at a consistent estimator `θhat n`, given the Lipschitz envelope on the score
  derivative already assumed for asymptotic normality.
* `I(θhat n) → I(θ₀)` in probability when `θ ↦ I(θ)` is continuous at `θ₀` (continuous
  mapping theorem for convergence in probability to a constant,
  `MeasureTheory.TendstoInMeasure.comp_const_of_continuousAt`).
* Wald's statistic `n ⟪Î (θhat n - θ₀), θhat n - θ₀⟫` and Rao's statistic `⟪Î⁻¹ Sₙ, Sₙ⟫`
  converge to `χ²_d` for **any** operator-valued estimators `Î n → I(θ₀)` in probability, in
  particular for the observed information.
* The likelihood-ratio statistic `2 (ℓₙ(θhat n) - ℓₙ(θ₀))` differs from the Wald statistic
  built with any consistent information estimate by a term tending to `0` in probability.

## Standing assumptions and what is not claimed

* The model hypotheses are those of `VectorInference`: i.i.d. data with law `p θ₀ ν`, an
  interior point `θ₀`, a Lipschitz envelope `M` on the score derivative on a ball of radius
  `δ > 0`, the centering and information identities assumed directly, and estimators
  `θhat n` that solve the likelihood equation with probability tending to one and are
  consistent (both are inputs, not derived).
* Information estimators enter through convergence in probability in operator norm together
  with a.e.-measurability. Where `Î n ω` is singular, `Ring.inverse` returns `0` and the
  score statistic takes the value `0`; this event has probability tending to `0` because
  `I(θ₀)` is invertible.
* Consistency of the observed information at `θhat n` needs no measurability of
  `(θ, x) ↦ D_θ score p θ x`. The Wald corollary that plugs it in assumes joint measurability,
  since the Slutsky step needs a measurable estimator.
* Only a simple null `θ = θ₀` is covered, and the likelihood-ratio statistic is evaluated at the
  root `θhat n`, as in `VectorInference`.

## Main results

* `measurable_ring_inverse`: `Ring.inverse` is measurable on a complete normed ring.
* `observedInformation`: `Ĵₙ(θ) = -(1/n) ∑_{i<n} D_θ score p θ (x i)`;
  `aestronglyMeasurable_observedInformation`, `aemeasurable_observedInformation_comp`.
* `tendstoInMeasure_observedInformation`: `Ĵₙ(θ₀) → I(θ₀)` in probability.
* `tendstoInMeasure_observedInformation_of_tendstoInMeasure`: `Ĵₙ(θhat n) → I(θ₀)`.
* `tendstoInMeasure_fisherInformation_comp`: `I(θhat n) → I(θ₀)` when `I` is continuous at `θ₀`.
* `tendstoInDistribution_waldStatistic_of_estimator`,
  `tendstoInDistribution_waldStatistic_observedInformation`: Wald with estimated information.
* `tendstoInDistribution_scoreStatistic_of_estimator`,
  `tendstoInDistribution_scoreStatistic_observedInformation`: Rao with estimated information.
* `tendstoInMeasure_two_mul_logLikelihood_sub_sub`,
  `tendstoInMeasure_two_mul_logLikelihood_sub_sub_of_estimator`: the likelihood-ratio statistic
  minus the Wald statistic (null or estimated information) tends to `0` in probability.

## Duplication and follow-up

`VectorInference` is outside this file's ownership, so some of its private material is copied
here; all copies are private and faithful. Follow-up once it may be edited:

* rewrite `VectorInference.tendstoInDistribution_two_mul_logLikelihood_sub` (Wilks) to call
  `tendstoInMeasure_two_mul_logLikelihood_sub_sub`, whose remainder proof repeats the one inside
  it, then delete the private copy `norm_sum_add_sum_apply_le'` here (twin of
  `VectorInference.norm_sum_add_sum_apply_le`);
* replace the note in the `VectorInference` module docstring that estimated-information
  versions and observed-information consistency "are not covered here" with a pointer to this
  file;
* delete the private copy `tendstoInMeasure_add_zero'` in `VectorInference` and use the public
  `MeasureTheory.tendstoInMeasure_add_zero` (in `MLEAsymptoticNormality`).

## References

* A. Wald, "Tests of statistical hypotheses concerning several parameters when the number of
  observations is large", Trans. Amer. Math. Soc. 54 (1943) 426–482.
* C. R. Rao, "Large sample tests of statistical hypotheses concerning several parameters with
  applications to problems of estimation", Proc. Cambridge Philos. Soc. 44 (1948) 50–57.
* B. Efron and D. V. Hinkley, "Assessing the accuracy of the maximum likelihood estimator:
  observed versus expected Fisher information", Biometrika 65 (1978) 457–487.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §5.6 and ch. 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)
open MathlibExt.Probability.Statistics.VectorInference

/-! ### Measurability of the inverse -/

/-- `Ring.inverse` is measurable on a complete normed ring with its Borel σ-algebra: it is
continuous on the open set of units and `0` off it. -/
theorem measurable_ring_inverse {R : Type*} [NormedRing R] [CompleteSpace R] [MeasurableSpace R]
    [BorelSpace R] : Measurable (Ring.inverse : R → R) := by
  classical
  have e : (Ring.inverse : R → R) = Set.piecewise {x : R | IsUnit x} Ring.inverse (fun _ => 0) :=
    funext fun x => by
      by_cases hx : IsUnit x
      · simp [Set.piecewise, hx]
      · simp [Set.piecewise, hx, Ring.inverse_non_unit]
  rw [e]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const Units.isOpen.measurableSet
  rintro _ ⟨u, rfl⟩
  exact (NormedRing.inverse_continuousAt u).continuousWithinAt

namespace MathlibExt.Probability.Statistics.EstimatedInformation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ### Observed information -/

/-- The **observed information** of a sample `x 0, …, x (n - 1)` at `θ`: minus the average of
the derivatives of the score, `Ĵₙ(θ) = -(1/n) ∑_{i<n} D_θ score p θ (x i)`. When the score is
the gradient of `θ ↦ log p θ x`, this is minus the average Hessian of the log-likelihood. For
`n = 0` it is `0` (Lean's `0⁻¹ = 0`). -/
noncomputable def observedInformation (p : E → 𝓧 → ℝ) (n : ℕ) (x : ℕ → 𝓧) (θ : E) :
    E →L[ℝ] E :=
  -((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, fderiv ℝ (fun t => score p t (x i)) θ)

omit [MeasurableSpace 𝓧] in
/-- The observed information of the empty sample is `0`. -/
theorem observedInformation_zero (p : E → 𝓧 → ℝ) (x : ℕ → 𝓧) (θ : E) :
    observedInformation p 0 x θ = 0 := by
  simp [observedInformation]

variable [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- The observed information at `θ₀` along an i.i.d. sample is a.e. strongly measurable. -/
theorem aestronglyMeasurable_observedInformation {p : E → 𝓧 → ℝ} {θ₀ : E} {X : ℕ → Ω → 𝓧}
    (hXm : ∀ i, AEMeasurable (X i) P)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀) (n : ℕ) :
    AEStronglyMeasurable (fun ω => observedInformation p n (fun i => X i ω) θ₀) P := by
  have h : AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range n, fderiv ℝ (fun t => score p t (X i ω)) θ₀) P :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      hs'_meas.aestronglyMeasurable.comp_aemeasurable (hXm i)
  exact (h.const_smul ((n : ℝ)⁻¹)).neg

omit [BorelSpace E] [IsProbabilityMeasure P] in
/-- The observed information at a random point `θhat` along a sample is a.e. measurable when
`(θ, x) ↦ D_θ score p θ x` is jointly measurable. -/
theorem aemeasurable_observedInformation_comp {p : E → 𝓧 → ℝ}
    (hDs_meas : Measurable fun q : E × 𝓧 => fderiv ℝ (fun t => score p t q.2) q.1)
    {X : ℕ → Ω → 𝓧} (hXm : ∀ i, AEMeasurable (X i) P) {θhat : Ω → E}
    (hθ_meas : AEMeasurable θhat P) (n : ℕ) :
    AEMeasurable (fun ω => observedInformation p n (fun i => X i ω) (θhat ω)) P := by
  have h : AEMeasurable
      (fun ω => ∑ i ∈ Finset.range n, fderiv ℝ (fun t => score p t (X i ω)) (θhat ω)) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => hDs_meas.comp_aemeasurable (hθ_meas.prodMk (hXm i))
  exact (h.const_smul ((n : ℝ)⁻¹)).neg

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Consistency of the observed information at `θ₀`.** For i.i.d. observations with law
`p θ₀ ν`, if `D_θ score p θ₀` is strongly measurable and integrable with
`E D_θ score p θ₀ = -I(θ₀)` (the information identity), then `Ĵₙ(θ₀) → I(θ₀)` in probability
(in operator norm). This is the vector form of
`LikelihoodRatioTests.tendstoInMeasure_observedInformation`. -/
theorem tendstoInMeasure_observedInformation {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀) :
    TendstoInMeasure P (fun n ω => observedInformation p n (fun i => X i ω) θ₀) atTop
      (fun _ => fisherInformation ν p θ₀) := by
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae
    (aestronglyMeasurable_observedInformation hXm hs'_meas) ?_
  filter_upwards [ae_tendsto_average hX_law hX_indep hs'_meas hs'_int] with ω hω
  rw [h_info] at hω
  simpa [observedInformation] using hω.neg

/-- **Consistency of the observed information at a consistent estimator.** In addition to the
hypotheses of `tendstoInMeasure_observedInformation`, assume the Lipschitz envelope
`‖D_θ score p θ x - D_θ score p θ₀ x‖ ≤ M x ‖θ - θ₀‖` on the ball of radius `δ > 0` about
`θ₀` with integrable `M` (as in `VectorInference`). Then for any a.e.-measurable estimators
`θhat n → θ₀` in probability, `Ĵₙ(θhat n) → I(θ₀)` in probability. No measurability of
`(θ, x) ↦ D_θ score p θ x` is needed.

Source: van der Vaart (1998), §5.6 (consistency of the plug-in observed information). -/
theorem tendstoInMeasure_observedInformation_of_tendstoInMeasure {ν : Measure 𝓧}
    {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀)) :
    TendstoInMeasure P (fun n ω => observedInformation p n (fun i => X i ω) (θhat n ω)) atTop
      (fun _ => fisherInformation ν p θ₀) := by
  set I := fisherInformation ν p θ₀
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  set M' : 𝓧 → ℝ := fun x => |M x| with hM'_def
  have hM'_meas : Measurable M' := continuous_abs.measurable.comp hM_meas
  have hM'_int : Integrable M' (lawOf ν p θ₀) := hM_int.abs
  set Mb : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (X i ω) with hMb_def
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, M' (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hM'_meas.comp_aemeasurable (hXm i)
    exact h.const_mul ((n : ℝ)⁻¹)
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M' x ∂(lawOf ν p θ₀)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable)
      (ae_tendsto_average hX_law hX_indep hM'_meas.stronglyMeasurable hM'_int)
  have hdθ : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖ * Mb n ω) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ (fun n => ((hθ_meas n).sub_const _).norm)
    simpa only [mul_comm] using h
  have h0 : TendstoInMeasure P
      (fun n ω => ‖observedInformation p n (fun i => X i ω) θ₀ - I‖) atTop 0 := by
    have h := tendstoInMeasure_observedInformation hX_law hX_indep hs'_meas hs'_int h_info
    rw [tendstoInMeasure_iff_norm] at h ⊢
    simpa using h
  have hV := tendstoInMeasure_add_zero h0 hrem
  have hG : Tendsto (fun n => P {ω | ‖θhat n ω - θ₀‖ < δ}ᶜ) atTop (𝓝 0) := by
    refine ((tendstoInMeasure_iff_dist.1 hcons) δ hδ).congr fun n => ?_
    congr 1
    ext ω
    simp [dist_eq_norm]
  have hW := tendstoInMeasure_zero_of_abs_le
    (W := fun n ω => ‖observedInformation p n (fun i => X i ω) (θhat n ω) - I‖) hV hG
    fun n ω hω => by
      simp only [Set.mem_ofPred_eq] at hω
      have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hω
      rw [abs_of_nonneg (norm_nonneg _)]
      have hdiff : ‖observedInformation p n (fun i => X i ω) (θhat n ω) -
          observedInformation p n (fun i => X i ω) θ₀‖ ≤ ‖θhat n ω - θ₀‖ * Mb n ω := by
        have e : observedInformation p n (fun i => X i ω) (θhat n ω) -
            observedInformation p n (fun i => X i ω) θ₀ =
            -((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
              (fderiv ℝ (fun t => score p t (X i ω)) (θhat n ω) -
                fderiv ℝ (fun t => score p t (X i ω)) θ₀)) := by
          simp only [observedInformation, Finset.sum_sub_distrib, smul_sub]
          abel
        rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
        have hsum : ‖∑ i ∈ Finset.range n, (fderiv ℝ (fun t => score p t (X i ω)) (θhat n ω) -
            fderiv ℝ (fun t => score p t (X i ω)) θ₀)‖ ≤
            (∑ i ∈ Finset.range n, M' (X i ω)) * ‖θhat n ω - θ₀‖ := by
          rw [Finset.sum_mul]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (hM (X i ω) _ hball).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
        calc (n : ℝ)⁻¹ * ‖∑ i ∈ Finset.range n,
              (fderiv ℝ (fun t => score p t (X i ω)) (θhat n ω) -
                fderiv ℝ (fun t => score p t (X i ω)) θ₀)‖
            ≤ (n : ℝ)⁻¹ * ((∑ i ∈ Finset.range n, M' (X i ω)) * ‖θhat n ω - θ₀‖) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = ‖θhat n ω - θ₀‖ * Mb n ω := by simp only [hMb_def, smul_eq_mul]; ring
      calc ‖observedInformation p n (fun i => X i ω) (θhat n ω) - I‖
          ≤ ‖observedInformation p n (fun i => X i ω) (θhat n ω) -
              observedInformation p n (fun i => X i ω) θ₀‖ +
            ‖observedInformation p n (fun i => X i ω) θ₀ - I‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖θhat n ω - θ₀‖ * Mb n ω + ‖observedInformation p n (fun i => X i ω) θ₀ - I‖ := by
            gcongr
        _ = _ := add_comm _ _
  rw [tendstoInMeasure_iff_norm] at hW ⊢
  simpa using hW

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- **Plug-in expected information.** If `θ ↦ I(θ)` is continuous at `θ₀` and
`θhat n → θ₀` in probability, then `I(θhat n) → I(θ₀)` in probability. -/
theorem tendstoInMeasure_fisherInformation_comp {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    (hI_cont : ContinuousAt (fisherInformation ν p) θ₀)
    {θhat : ℕ → Ω → E} (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀)) :
    TendstoInMeasure P (fun n ω => fisherInformation ν p (θhat n ω)) atTop
      (fun _ => fisherInformation ν p θ₀) :=
  hcons.comp_const_of_continuousAt hI_cont

/-- A Gaussian limit for the score: a linear map `A` with `⟪A z, t⟫ ~ N(0, ⟪I(θ₀) t, t⟫)` under
`N(0, Id)`, built from a measurable, centered, square-integrable score. -/
private theorem exists_hasLaw_inner_fisherInformation {ν : Measure 𝓧} {p : E → 𝓧 → ℝ}
    {θ₀ : E} {X₀ : Ω → 𝓧} (hX₀ : HasLaw X₀ (lawOf ν p θ₀) P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0) :
    ∃ A : E →L[ℝ] E, ∀ t, HasLaw (fun z => ⟪A z, t⟫)
      (gaussianReal 0 (⟪fisherInformation ν p θ₀ t, t⟫).toNNReal) (stdGaussian E) := by
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal (hX₀.memLp_comp hs)
  refine ⟨A, fun t => ?_⟩
  have h := hA t
  rwa [show (fun ω => ⟪(score p θ₀ ∘ X₀) ω, t⟫) = fun ω => ⟪score p θ₀ (X₀ ω), t⟫ from rfl,
    variance_inner_score hX₀ hs_meas hs_sq hs_mean t] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic form `(v, A) ↦ ⟪A v, v⟫` is jointly continuous. -/
private theorem continuous_inner_apply_self :
    Continuous fun z : E × (E →L[ℝ] E) => ⟪z.2 z.1, z.1⟫ :=
  (isBoundedBilinearMap_apply.continuous.comp continuous_swap).inner continuous_fst

/-- **Wald's test with an estimated information, vector parameter.** Under the hypotheses of
`VectorInference.tendstoInDistribution_waldStatistic`, let `Î n` be any a.e.-measurable
operator-valued estimators with `Î n → I(θ₀)` in probability (operator norm), for example the
observed information `Ĵₙ(θhat n)` (`tendstoInMeasure_observedInformation_of_tendstoInMeasure`),
`Ĵₙ(θ₀)`, or `I(θhat n)` when `I` is continuous at `θ₀`
(`tendstoInMeasure_fisherInformation_comp`). Then the Wald statistic
`n ⟪Î n (θhat n - θ₀), θhat n - θ₀⟫` converges in distribution to `χ²_d`, `d = dim E ≥ 1`.

Source: Wald (1943); van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_waldStatistic_of_estimator
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Ihat : ℕ → Ω → E →L[ℝ] E} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => fisherInformation ν p θ₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => n * ⟪Ihat n ω (θhat n ω - θ₀), θhat n ω - θ₀⟫)
      atTop Q (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  have hI : IsUnit I := isUnit_of_inner_self_pos hI_pos
  obtain ⟨A, hAI⟩ := exists_hasLaw_inner_fisherInformation (hX_law 0) hs_meas hs_sq hs_mean
  have h := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  have h2 := h.continuous_comp_prodMk_of_tendstoInMeasure_const continuous_inner_apply_self
    hIhat hIhat_meas
  have hchi := hasLaw_inner_inverse_chiSquare (inner_fisherInformation_comm ν p θ₀) hI_pos hd
    A.continuous.aemeasurable hAI
  refine (h2.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun z => rfl)).of_map_eq
    hQ.aemeasurable ?_
  · simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · rw [hQ.map_eq, ← hchi.map_eq]
    congr 1
    funext z
    simp only
    rw [apply_inverse_apply hI, real_inner_comm]

/-- **Rao's score test with an estimated information, vector parameter.** Under the hypotheses
of `VectorInference.tendstoInDistribution_scoreStatistic`, let `Î n` be any a.e.-measurable
estimators with `Î n → I(θ₀)` in probability (operator norm), for example the observed
information `Ĵₙ(θ₀)` (`tendstoInMeasure_observedInformation`). Then
`⟪Î n⁻¹ Sₙ, Sₙ⟫ → χ²_d`, `Sₙ = n^{-1/2} ∑_{i<n} score p θ₀ (X i)`, `d = dim E ≥ 1`. The inverse
is `Ring.inverse`, which is `0` at singular `Î n ω`; that event has probability tending to `0`.

Source: Rao (1948); van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_scoreStatistic_of_estimator {ν : Measure 𝓧} {p : E → 𝓧 → ℝ}
    {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {Ihat : ℕ → Ω → E →L[ℝ] E} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => fisherInformation ν p θ₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Ihat n ω) ((√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)⟫)
      atTop Q (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  have hI : IsUnit I := isUnit_of_inner_self_pos hI_pos
  obtain ⟨A, hAI⟩ := exists_hasLaw_inner_fisherInformation (hX_law 0) hs_meas hs_sq hs_mean
  have h := tendstoInDistribution_score hX_law hX_indep hs_meas hs_sq hs_mean
    A.continuous.aemeasurable hAI
  obtain ⟨u, hu⟩ := hI
  have hK : TendstoInMeasure P (fun n ω => Ring.inverse (Ihat n ω)) atTop
      (fun _ => Ring.inverse I) :=
    hIhat.comp_const_of_continuousAt (hu ▸ NormedRing.inverse_continuousAt u)
  have hK_meas : ∀ n, AEMeasurable (fun ω => Ring.inverse (Ihat n ω)) P := fun n =>
    measurable_ring_inverse.comp_aemeasurable (hIhat_meas n)
  have h2 := h.continuous_comp_prodMk_of_tendstoInMeasure_const continuous_inner_apply_self
    hK hK_meas
  have hchi := hasLaw_inner_inverse_chiSquare (inner_fisherInformation_comm ν p θ₀) hI_pos hd
    A.continuous.aemeasurable hAI
  exact h2.of_map_eq hQ.aemeasurable (by rw [hQ.map_eq, ← hchi.map_eq])

/-! ### The likelihood ratio and the Wald statistic with estimated information -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace 𝓧] in
/-- The summed first-order Taylor bound at a root `θ` in the ball:
`‖∑ ψ θ₀ (xᵢ) + (∑ Dψ θ₀ (xᵢ)) (θ - θ₀)‖ ≤ (∑ M (xᵢ)) ‖θ - θ₀‖²`. -/
private theorem norm_sum_add_sum_apply_le' {ψ : E → 𝓧 → E} {θ₀ : E} {δ : ℝ}
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓧 → ℝ}
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M x * ‖θ - θ₀‖)
    (n : ℕ) (xs : ℕ → 𝓧) {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ)
    (hroot : ∑ i ∈ Finset.range n, ψ θ (xs i) = 0) :
    ‖∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
        (∑ i ∈ Finset.range n, fderiv ℝ (fun t => ψ t (xs i)) θ₀) (θ - θ₀)‖ ≤
      (∑ i ∈ Finset.range n, M (xs i)) * ‖θ - θ₀‖ ^ 2 := by
  have e : ∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
      (∑ i ∈ Finset.range n, fderiv ℝ (fun t => ψ t (xs i)) θ₀) (θ - θ₀) =
      -∑ i ∈ Finset.range n, (ψ θ (xs i) - ψ θ₀ (xs i) -
        fderiv ℝ (fun t => ψ t (xs i)) θ₀ (θ - θ₀)) := by
    rw [sum_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hroot]
    abel
  rw [e, norm_neg, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact norm_sub_sub_fderiv_le (f := fun t => ψ t (xs i)) (hψ_diff (xs i)) (hM (xs i)) hθ

/-- **Quadratic expansion of the log-likelihood ratio, vector parameter.** Under the hypotheses
of `VectorInference.tendstoInDistribution_two_mul_logLikelihood_sub` (without the joint
measurability of `p`, the positive definiteness and `dim E ≥ 1`; only nonsingularity of
`I(θ₀)` is used), the likelihood-ratio statistic at the root minus the null-information Wald
statistic tends to `0` in probability:
`2 (ℓₙ(θhat n) - ℓₙ(θ₀)) - n ⟪I(θ₀) (θhat n - θ₀), θhat n - θ₀⟫ → 0`,
`ℓₙ θ = ∑_{i<n} log p θ (X i)`. This is the vector form of
`LikelihoodRatioTests.tendstoInMeasure_two_mul_logLikelihood_sub_sub`.

Source: the second-order expansion of Wilks (1938); van der Vaart (1998), Theorem 16.7. -/
theorem tendstoInMeasure_two_mul_logLikelihood_sub_sub
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) -
        n * ⟪fisherInformation ν p θ₀ (θhat n ω - θ₀), θhat n ω - θ₀⟫)
      atTop 0 := by
  set I := fisherInformation ν p θ₀
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  obtain ⟨A, hAI⟩ := exists_hasLaw_inner_fisherInformation (hX_law 0) hs_meas hs_sq hs_mean
  have hT := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  -- notation
  set H : 𝓧 → E →L[ℝ] E := fun x => fderiv ℝ (fun t => score p t x) θ₀ with hH_def
  set M' : 𝓧 → ℝ := fun x => |M x| with hM'_def
  have hM'_meas : Measurable M' := continuous_abs.measurable.comp hM_meas
  have hM'_int : Integrable M' (lawOf ν p θ₀) := hM_int.abs
  have hM' : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M' x * ‖θ - θ₀‖ :=
    fun x θ hθ => (hM x θ hθ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  set L : ℕ → Ω → ℝ := fun n ω => 2 * ∑ i ∈ Finset.range n,
    (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) with hL_def
  set W : ℕ → Ω → ℝ := fun n ω => n * ⟪I (θhat n ω - θ₀), θhat n ω - θ₀⟫ with hW_def
  set T : ℕ → Ω → E := fun n ω => √n • (θhat n ω - θ₀) with hT_def
  set B : ℕ → Ω → E →L[ℝ] E := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (X i ω)
    with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (X i ω) with hMb_def
  set η : ℕ → Ω → ℝ := fun n ω => ‖B n ω - (-I)‖ + 4 * (‖θhat n ω - θ₀‖ * Mb n ω) with hη_def
  -- measurability
  have hB_sm : ∀ n, AEStronglyMeasurable (B n) P := fun n => by
    have h : AEStronglyMeasurable (fun ω => ∑ i ∈ Finset.range n, H (X i ω)) P :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        hs'_meas.aestronglyMeasurable.comp_aemeasurable (hXm i)
    exact h.const_smul ((n : ℝ)⁻¹)
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, M' (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hM'_meas.comp_aemeasurable (hXm i)
    exact h.const_mul ((n : ℝ)⁻¹)
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    ((hB_sm n).sub aestronglyMeasurable_const).norm.aemeasurable.add
      ((((hθ_meas n).sub_const _).norm.mul (hMb_meas n)).const_mul 4)
  -- laws of large numbers
  have hB : TendstoInMeasure P B atTop (fun _ => -I) := by
    have h := tendstoInMeasure_of_tendsto_ae hB_sm
      (ae_tendsto_average hX_law hX_indep hs'_meas hs'_int)
    rwa [h_info] at h
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M' x ∂(lawOf ν p θ₀)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable)
      (ae_tendsto_average hX_law hX_indep hM'_meas.stronglyMeasurable hM'_int)
  have hBD : TendstoInMeasure P (fun n ω => ‖B n ω - (-I)‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => 4 * (‖θhat n ω - θ₀‖ * Mb n ω)) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ (fun n => ((hθ_meas n).sub_const _).norm)
    have h' : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖ * Mb n ω) atTop 0 := by
      simpa only [mul_comm] using h
    rw [tendstoInMeasure_iff_norm] at h' ⊢
    intro ε hε
    refine (h' (ε / 4) (by positivity)).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    constructor <;> intro h <;> linarith
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero hBD hrem
  -- good events
  set G : ℕ → Set Ω := fun n => {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) = 0} ∩
    {ω | ‖θhat n ω - θ₀‖ < δ} with hG_def
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h3 := hroot.add h1
    simp only [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => ?_
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, dist_eq_norm]
    exact hω
  -- deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n, |L n ω - W n ω| ≤ ‖T n ω‖ ^ 2 * η n ω := by
    intro n ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hL_def, hW_def, hT_def]
    obtain ⟨hroot', hclose⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hclose
    set d := θhat n ω - θ₀ with hd
    set S0 := ∑ i ∈ Finset.range n, score p θ₀ (X i ω) with hS0
    set Hs := ∑ i ∈ Finset.range n, H (X i ω) with hHs_def
    set SM := ∑ i ∈ Finset.range n, M' (X i ω) with hSM_def
    set e : ℕ → ℝ := fun i => Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω)) -
      ⟪score p θ₀ (X i ω), d⟫ - ⟪H (X i ω) d, d⟫ / 2 with he_def
    have he : ∀ i, |e i| ≤ M' (X i ω) * ‖d‖ ^ 3 := fun i =>
      abs_log_sub_sub_sub_le (hℓ_diff (X i ω)) (hs_diff (X i ω)) (hM' (X i ω)) hball
    have htay : ‖S0 + Hs d‖ ≤ SM * ‖d‖ ^ 2 :=
      norm_sum_add_sum_apply_le' hs_diff hM' n (fun i => X i ω) hball hroot'
    have hid : L n ω - W n ω =
        2 * ∑ i ∈ Finset.range n, e i + 2 * ⟪S0 + Hs d, d⟫ - ⟪(Hs + (n : ℝ) • I) d, d⟫ := by
      simp only [hL_def, hW_def, he_def, hS0, hHs_def, add_apply,
        smul_apply, inner_add_left, real_inner_smul_left,
        sum_apply, sum_inner, Finset.sum_sub_distrib, ← Finset.sum_div]
      ring
    have h1 : |∑ i ∈ Finset.range n, e i| ≤ SM * ‖d‖ ^ 3 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hSM_def, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => he i
    have h2 : |⟪S0 + Hs d, d⟫| ≤ SM * ‖d‖ ^ 3 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖S0 + Hs d‖ * ‖d‖ ≤ SM * ‖d‖ ^ 2 * ‖d‖ :=
            mul_le_mul_of_nonneg_right htay (norm_nonneg _)
        _ = SM * ‖d‖ ^ 3 := by ring
    have h3 : |⟪(Hs + (n : ℝ) • I) d, d⟫| ≤ ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖(Hs + (n : ℝ) • I) d‖ * ‖d‖ ≤ ‖Hs + (n : ℝ) • I‖ * ‖d‖ * ‖d‖ :=
            mul_le_mul_of_nonneg_right ((Hs + (n : ℝ) • I).le_opNorm d) (norm_nonneg _)
        _ = ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 := by ring
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hSM : SM = n * Mb n ω := by
      simp only [hMb_def, smul_eq_mul, hSM_def]
      field_simp
    have hHs : Hs + (n : ℝ) • I = (n : ℝ) • (B n ω - -I) := by
      simp only [hB_def, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hn0, one_smul,
        hHs_def]
    have hT2 : ‖T n ω‖ ^ 2 = n * ‖d‖ ^ 2 := by
      simp only [hT_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      rfl
    rw [hid]
    obtain ⟨h1l, h1r⟩ := abs_le.1 h1
    obtain ⟨h2l, h2r⟩ := abs_le.1 h2
    obtain ⟨h3l, h3r⟩ := abs_le.1 h3
    have hfin : 2 * (SM * ‖d‖ ^ 3) + 2 * (SM * ‖d‖ ^ 3) + ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 =
        ‖T n ω‖ ^ 2 * η n ω := by
      rw [hHs, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < n), hSM, hT2]
      simp only [hη_def]
      ring
    rw [← hfin, abs_le]
    constructor <;> linarith
  -- conclusion
  have hV : TendstoInMeasure P (fun n ω => ‖T n ω‖ ^ 2 * η n ω) atTop 0 :=
    (hT.continuous_comp (g := fun v => ‖v‖ ^ 2) (by fun_prop)).mul_tendstoInMeasure_zero hη
      hη_meas
  exact tendstoInMeasure_zero_of_abs_le hV hG hbound

/-- **Likelihood ratio versus Wald with estimated information.** Under the hypotheses of
`tendstoInMeasure_two_mul_logLikelihood_sub_sub`, for any a.e.-measurable operator-valued
estimators `Î n → I(θ₀)` in probability (for example the observed information `Ĵₙ(θhat n)`),
`2 (ℓₙ(θhat n) - ℓₙ(θ₀)) - n ⟪Î n (θhat n - θ₀), θhat n - θ₀⟫ → 0` in probability: the
likelihood-ratio statistic and the Wald statistic with estimated information are asymptotically
equivalent, so either may be referred to `χ²_d`.

Source: van der Vaart (1998), ch. 16; Efron and Hinkley (1978). -/
theorem tendstoInMeasure_two_mul_logLikelihood_sub_sub_of_estimator
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Ihat : ℕ → Ω → E →L[ℝ] E} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => fisherInformation ν p θ₀)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) -
        n * ⟪Ihat n ω (θhat n ω - θ₀), θhat n ω - θ₀⟫)
      atTop 0 := by
  set I := fisherInformation ν p θ₀
  have hLW := tendstoInMeasure_two_mul_logLikelihood_sub_sub hδ hX_law hX_indep hℓ_diff hs_diff
    hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI hθ_meas hroot hcons
  obtain ⟨A, hAI⟩ := exists_hasLaw_inner_fisherInformation (hX_law 0) hs_meas hs_sq hs_mean
  have hT := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  have hg : Continuous fun z : E × (E →L[ℝ] E) => ⟪(I - z.2) z.1, z.1⟫ :=
    ((isBoundedBilinearMap_apply.continuous.comp
      ((continuous_const.sub continuous_snd).prodMk continuous_fst)).inner continuous_fst)
  have h2 := hT.continuous_comp_prodMk_of_tendstoInMeasure_const hg hIhat hIhat_meas
  have hWW : TendstoInMeasure P
      (fun (n : ℕ) ω => ⟪(I - Ihat n ω) (√n • (θhat n ω - θ₀)), √n • (θhat n ω - θ₀)⟫)
      atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendstoInDistribution_const
      (h2.congr (fun n => ae_of_all _ fun ω => rfl) (ae_of_all _ fun z => by simp))
  refine (tendstoInMeasure_add_zero hLW hWW).congr_left fun n => ae_of_all _ fun ω => ?_
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, sub_apply, inner_sub_left]
  rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  ring

/-! ### Corollaries with the observed information -/

/-- **Wald's test with the observed information at the estimator.** Under the hypotheses of
`tendstoInDistribution_waldStatistic_of_estimator` (without `Î`), if moreover
`(θ, x) ↦ D_θ score p θ x` is jointly measurable, the Wald statistic built with the observed
information at the estimator, `n ⟪Ĵₙ(θhat n) (θhat n - θ₀), θhat n - θ₀⟫`, converges in
distribution to `χ²_d`. -/
theorem tendstoInDistribution_waldStatistic_observedInformation
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hDs_meas : Measurable fun q : E × 𝓧 => fderiv ℝ (fun t => score p t q.2) q.1)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => n * ⟪observedInformation p n (fun i => X i ω) (θhat n ω)
        (θhat n ω - θ₀), θhat n ω - θ₀⟫)
      atTop Q (fun _ => P) P' := by
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀ :=
    (hDs_meas.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  exact tendstoInDistribution_waldStatistic_of_estimator hδ hX_law hX_indep hs_diff hM_meas
    hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos hd hθ_meas hroot hcons
    (fun n => aemeasurable_observedInformation_comp hDs_meas hXm (hθ_meas n) n)
    (tendstoInMeasure_observedInformation_of_tendstoInMeasure hδ hX_law hX_indep
      hM_meas hM_int hM hs'_meas hs'_int h_info hθ_meas hcons) hQ

/-- **Rao's score test with the observed information at `θ₀`.** Under the hypotheses of
`tendstoInDistribution_scoreStatistic_of_estimator` (without `Î`), if `D_θ score p θ₀` is
strongly measurable and integrable with `E D_θ score p θ₀ = -I(θ₀)`, then
`⟪Ĵₙ(θ₀)⁻¹ Sₙ, Sₙ⟫ → χ²_d`. -/
theorem tendstoInDistribution_scoreStatistic_observedInformation {ν : Measure 𝓧}
    {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ⟪Ring.inverse (observedInformation p n (fun i => X i ω) θ₀)
            ((√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)⟫)
      atTop Q (fun _ => P) P' := by
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  exact tendstoInDistribution_scoreStatistic_of_estimator hX_law hX_indep hs_meas hs_sq hs_mean
    hI_pos hd (fun n => (aestronglyMeasurable_observedInformation hXm hs'_meas n).aemeasurable)
    (tendstoInMeasure_observedInformation hX_law hX_indep hs'_meas hs'_int h_info) hQ

end MathlibExt.Probability.Statistics.EstimatedInformation
