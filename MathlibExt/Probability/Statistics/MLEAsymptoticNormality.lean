/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FisherInformation
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw

/-!
# Asymptotic normality of the maximum-likelihood estimator

Let `X 0, X 1, …` be i.i.d. observations and let `ψ θ x` be an estimating function with
`E ψ θ₀ (X 0) = 0`. Under Cramér's regularity conditions (two derivatives of `ψ` in `θ` on a
neighborhood of `θ₀`, the second one bounded by an integrable envelope `M`), every consistent
sequence `θhat n` of roots of the estimating equation `∑_{i<n} ψ θ (X i) = 0` satisfies
`√n (θhat n - θ₀) → N(0, E ψ² / (E ∂_θ ψ)²)` in distribution. Taking `ψ` to be the score
`∂_θ log p θ x` of a positive density family `p` and using the Bartlett identities
`E ψ = 0`, `E ∂_θ ψ = -I(θ₀)` gives the asymptotic normality of maximum likelihood:
`√n (θhat n - θ₀) → N(0, 1 / I(θ₀))`.

The proof Taylor-expands the estimating equation around `θ₀`, applies the central limit
theorem to `n^{-1/2} ∑ ψ θ₀ (X i)`, the strong law to `n⁻¹ ∑ ∂_θ ψ θ₀ (X i)` and to
`n⁻¹ ∑ M (X i)`, and concludes with Slutsky's theorem (in Mathlib as
`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`).

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendstoInDistribution_const`: convergence in distribution
  to a constant implies convergence in probability.
* `MeasureTheory.TendstoInDistribution.mul_tendstoInMeasure_zero`: a sequence converging in
  distribution times a sequence converging in probability to `0` converges in probability
  to `0`.
* `MeasureTheory.tendstoInMeasure_zero_of_abs_le`: domination by a sequence tending to `0` in
  probability on events whose probability tends to one.
* `tendstoInDistribution_score`: the central limit theorem for the score,
  `n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (X i) → N(0, I(θ₀))`.
* `tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation`: asymptotic normality of a
  consistent root of an estimating equation (one-dimensional Z-estimator).
* `tendstoInDistribution_sqrt_mul_sub_maximumLikelihood`: asymptotic normality of a
  consistent root of the likelihood equation, with limit variance `1 / I(θ₀)`.

## References

* H. Cramér, *Mathematical Methods of Statistics* (1946), §33.3.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed. (1998), §6.3,
  Theorem 6.3.10 (Theorem 3.10 of ch. 6).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), ch. 5, Theorem 5.41.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MeasureTheory

variable {ι Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {l : Filter ι}

/-- **Convergence in distribution to a constant implies convergence in probability.** If the
random variables `X i` on one probability space converge in distribution to the constant `c`,
then they converge to `c` in probability. -/
theorem tendstoInMeasure_of_tendstoInDistribution_const [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ι → Ω → E} {c : E} (h : TendstoInDistribution X l (fun _ : Ω' => c) (fun _ => P) P') :
    TendstoInMeasure P X l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set F : Set E := {y | ε ≤ dist y c}
  have hF : IsClosed F := isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF
  have hc : (P'.map fun _ : Ω' => c) F = 0 := by
    rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_apply' _ hF.measurableSet]
    simp [F, hε.not_ge]
  simp only [ProbabilityMeasure.coe_mk, hc] at hlim
  have heq : ∀ i, P {ω | ε ≤ dist (X i ω) c} = (P.map (X i)) F := fun i => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable i) hF.measurableSet]
    rfl
  simp_rw [heq]
  refine tendsto_order.2 ⟨fun a ha => absurd ha ENNReal.not_lt_zero, fun a ha => ?_⟩
  exact eventually_lt_of_limsup_lt (hlim.trans_lt ha)

/-- A sequence `A i` converging in distribution, times a sequence `η i` converging in
probability to `0`, converges in probability to `0` (a consequence of Slutsky's theorem). -/
theorem TendstoInDistribution.mul_tendstoInMeasure_zero [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] [l.IsCountablyGenerated] {A η : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hA : TendstoInDistribution A l Z (fun _ => P) P') (hη : TendstoInMeasure P η l 0)
    (hη_meas : ∀ i, AEMeasurable (η i) P) :
    TendstoInMeasure P (fun i ω => A i ω * η i ω) l 0 := by
  have h := hA.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : ℝ × ℝ => x.1 * x.2) (by fun_prop) (c := 0) hη hη_meas
  simp only [mul_zero] at h
  exact tendstoInMeasure_of_tendstoInDistribution_const h

/-- If `|W i| ≤ V i` on events `G i` whose complements have probability tending to `0`, and
`V i` tends to `0` in probability, then `W i` tends to `0` in probability. -/
theorem tendstoInMeasure_zero_of_abs_le {W V : ι → Ω → ℝ} {G : ι → Set Ω}
    (hV : TendstoInMeasure P V l 0) (hG : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0))
    (hle : ∀ i, ∀ ω ∈ G i, |W i ω| ≤ V i ω) :
    TendstoInMeasure P W l 0 := by
  rw [tendstoInMeasure_iff_norm] at hV ⊢
  intro ε hε
  have h2 : Tendsto (fun i => P (G i)ᶜ + P {ω | ε ≤ ‖V i ω - (0 : Ω → ℝ) ω‖}) l (𝓝 0) := by
    simpa using hG.add (hV ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_cases hG' : ω ∈ G i
  · exact Or.inr (hω.trans ((hle i ω hG').trans (le_abs_self _)))
  · exact Or.inl hG'

/-- A sum of two sequences tending to `0` in probability tends to `0` in probability. -/
private theorem tendstoInMeasure_add_zero {U V : ι → Ω → ℝ}
    (hU : TendstoInMeasure P U l 0) (hV : TendstoInMeasure P V l 0) :
    TendstoInMeasure P (fun i ω => U i ω + V i ω) l 0 := by
  rw [tendstoInMeasure_iff_norm] at hU hV ⊢
  intro ε hε
  have h2 := (hU (ε / 2) (by positivity)).add (hV (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_add_le (U i ω) (V i ω)]

end MeasureTheory

namespace MathlibExt.Probability.Statistics.MLEAsymptoticNormality

open MathlibExt.Probability.Statistics.FisherInformation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The **score** `∂_θ log p θ x` of a one-parameter family of densities `p`. -/
noncomputable def score (p : ℝ → 𝓧 → ℝ) (θ : ℝ) (x : 𝓧) : ℝ :=
  deriv (fun t => Real.log (p t x)) θ

/-- For a positive density family, `E_θ [score²] = I(θ)`: the Fisher information of
`FisherInformation.fisherInformation` is the second moment of the score under `p θ ν`. -/
theorem integral_score_sq {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ) :
    ∫ x, score p θ x ^ 2 ∂lawOf ν p θ = fisherInformation ν p θ := by
  rw [lawOf, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top), fisherInformation]
  congr 1; funext x
  have hs : score p θ x = deriv (fun t => p t x) θ / p θ x :=
    ((hp_diff x).hasDerivAt.log (hp_pos x).ne').deriv
  rw [ENNReal.toReal_ofReal (hp_pos x).le, smul_eq_mul, hs]
  have := (hp_pos x).ne'
  field_simp

/-- **Central limit theorem for the score.** For i.i.d. observations with law `p θ₀ ν`, a
positive density family differentiable in `θ` at `θ₀`, a measurable score with mean zero and
`∫ score² d(p θ₀ ν) < ∞`, the normalized score `n^{-1/2} ∑_{i<n} score p θ₀ (X i)` converges in
distribution to `N(0, I(θ₀))`.

Source: Lehmann & Casella (1998), §6.3; van der Vaart (1998), ch. 5. -/
theorem tendstoInDistribution_score {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_pos : ∀ x, 0 < p θ₀ x) (hp_meas : Measurable (p θ₀))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (fisherInformation ν p θ₀).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X i ω)) atTop Y
      (fun _ => P) P' := by
  have : IsProbabilityMeasure (lawOf ν p θ₀) :=
    (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  set Z : ℕ → Ω → ℝ := fun i => score p θ₀ ∘ X i
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    (⟨(hX_law i).aemeasurable, (hX_law 0).aemeasurable,
      (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ : IdentDistrib (X i) (X 0) P P).comp
      hs_meas
  have hmean : P[Z 0] = 0 := by
    rw [← hs_mean]; exact (hX_law 0).integral_comp hs_meas.aestronglyMeasurable
  have hsq : P[fun ω => Z 0 ω ^ 2] = fisherInformation ν p θ₀ := by
    rw [← integral_score_sq hp_pos hp_meas hp_diff]
    exact (hX_law 0).integral_comp (f := fun x => score p θ₀ x ^ 2)
      (hs_meas.pow_const 2).aestronglyMeasurable
  have hL2 : MemLp (Z 0) 2 P := by
    have h1 : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
      (memLp_two_iff_integrable_sq hs_meas.aestronglyMeasurable).2 hs_sq
    exact (hX_law 0).memLp_comp h1
  have hvar : Var[Z 0; P] = fisherInformation ν p θ₀ := by
    rw [variance_of_integral_eq_zero hL2.aemeasurable hmean]; exact hsq
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (X := Z) (Y := Y)
    (by rwa [hvar]) hL2 (hX_indep.comp (fun _ => score p θ₀) (fun _ => hs_meas)) hident
  have hmean' : ∫ ω, score p θ₀ (X 0 ω) ∂P = 0 := hmean
  simpa [hmean', Z] using h

open Set in
/-- Second-order Taylor bound from a bound `m` on the second derivative on a ball. -/
private theorem abs_sub_sub_mul_deriv_le {f : ℝ → ℝ} {θ₀ δ θ m : ℝ}
    (hf : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ f t)
    (hf' : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (deriv f) t)
    (hm : ∀ t ∈ Metric.ball θ₀ δ, |deriv (deriv f) t| ≤ m) (hθ : θ ∈ Metric.ball θ₀ δ) :
    |f θ - f θ₀ - (θ - θ₀) * deriv f θ₀| ≤ m * (θ - θ₀) ^ 2 := by
  have h0 : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hθ)
  have hsub : uIcc θ₀ θ ⊆ Metric.ball θ₀ δ := by
    rw [Real.ball_eq_Ioo] at h0 hθ ⊢
    exact ordConnected_Ioo.uIcc_subset h0 hθ
  -- first-derivative increments
  have h1 : ∀ t ∈ uIcc θ₀ θ, |deriv f t - deriv f θ₀| ≤ m * |θ - θ₀| := fun t ht => by
    have := (convex_ball θ₀ δ).norm_image_sub_le_of_norm_deriv_le hf' (fun s hs => by
      rw [Real.norm_eq_abs]; exact hm s hs) h0 (hsub ht)
    simp only [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht)
      ((abs_nonneg _).trans (hm θ₀ h0)))
  set g : ℝ → ℝ := fun t => f t - (t - θ₀) * deriv f θ₀
  have hg : ∀ t ∈ uIcc θ₀ θ, HasDerivAt g (deriv f t - deriv f θ₀) t := fun t ht => by
    have := ((hf t (hsub ht)).hasDerivAt.fun_sub
      (((hasDerivAt_id t).sub_const θ₀).mul_const (deriv f θ₀)))
    simpa only [id, one_mul] using this
  have key := (convex_uIcc θ₀ θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) (fun t ht => by
      rw [Real.norm_eq_abs]; exact h1 t ht) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, g, sub_self, zero_mul, sub_zero] at key
  calc |f θ - f θ₀ - (θ - θ₀) * deriv f θ₀| = |f θ - (θ - θ₀) * deriv f θ₀ - f θ₀| := by
        ring_nf
    _ ≤ m * |θ - θ₀| * |θ - θ₀| := key
    _ = m * (θ - θ₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Asymptotic normality of a consistent root of an estimating equation** (one-dimensional
Z-estimator under Cramér-type conditions). Let `X 0, X 1, …` be i.i.d. with law `μX` and let
`ψ θ x` satisfy, for every `x` and every `θ` in the ball of radius `δ > 0` about `θ₀`: `ψ · x`
and `∂_θ ψ · x` are differentiable at `θ`, and `|∂²_θ ψ θ x| ≤ M x` with `M` integrable. Assume
`E ψ θ₀ = 0`, `E ψ θ₀² < ∞`, `∂_θ ψ θ₀` integrable with `E ∂_θ ψ θ₀ ≠ 0`. Let `θhat n` be
estimators that solve `∑_{i<n} ψ θ (X i) = 0` with probability tending to one and converge to
`θ₀` in probability. Then `√n (θhat n - θ₀)` converges in distribution to
`N(0, E ψ θ₀² / (E ∂_θ ψ θ₀)²)`.

Source: van der Vaart (1998), Theorem 5.41 (one-dimensional case, with the third-derivative
envelope of Cramér (1946), §33.3); Lehmann & Casella (1998), §6.3. -/
theorem tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation
    {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P)
    {ψ : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    (hψ'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => ψ s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M μX)
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => ψ s x) t) θ| ≤ M x)
    (hψ_meas : Measurable (ψ θ₀)) (hψ_sq : Integrable (fun x => ψ θ₀ x ^ 2) μX)
    (hψ_mean : ∫ x, ψ θ₀ x ∂μX = 0)
    (hψ'_meas : Measurable fun x => deriv (fun t => ψ t x) θ₀)
    (hψ'_int : Integrable (fun x => deriv (fun t => ψ t x) θ₀) μX)
    (hJ : ∫ x, deriv (fun t => ψ t x) θ₀ ∂μX ≠ 0)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, ψ (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 ((∫ x, ψ θ₀ x ^ 2 ∂μX) /
      (∫ x, deriv (fun t => ψ t x) θ₀ ∂μX) ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (θhat n ω - θ₀)) atTop Y (fun _ => P) P' := by
  have : IsProbabilityMeasure μX := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  set ψ' : 𝓧 → ℝ := fun x => deriv (fun t => ψ t x) θ₀ with hψ'_def
  set J : ℝ := -∫ x, ψ' x ∂μX with hJ_def
  have hJ0 : J ≠ 0 := neg_ne_zero.2 hJ
  have hθ₀ : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self hδ
  have hM0 : ∀ x, 0 ≤ M x := fun x => (abs_nonneg _).trans (hM x θ₀ hθ₀)
  set A : ℕ → Ω → ℝ := fun n ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, ψ θ₀ (X i ω) with hA_def
  set B : ℕ → Ω → ℝ := fun n ω => -((∑ i ∈ Finset.range n, ψ' (X i ω)) / n) with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, M (X i ω)) / n with hMb_def
  set T : ℕ → Ω → ℝ := fun n ω => √n * (θhat n ω - θ₀) with hT_def
  set η : ℕ → Ω → ℝ := fun n ω => |B n ω - J| + |θhat n ω - θ₀| * Mb n ω with hη_def
  -- measurability
  have hA_meas : ∀ n, AEMeasurable (A n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hψ_meas.comp_aemeasurable (hXm i)).const_mul _
  have hB_meas : ∀ n, AEMeasurable (B n) P := fun n =>
    ((Finset.aemeasurable_fun_sum _ fun i _ => hψ'_meas.comp_aemeasurable (hXm i)).div_const
      _).neg
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hM_meas.comp_aemeasurable (hXm i)).div_const _
  have hT_meas : ∀ n, AEMeasurable (T n) P := fun n =>
    ((hθ_meas n).sub_const _).const_mul _
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    (continuous_abs.measurable.comp_aemeasurable ((hB_meas n).sub_const _)).add
      ((continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _)).mul (hMb_meas n))
  -- identically distributed transforms
  have hident : ∀ (g : 𝓧 → ℝ), Measurable g → ∀ i,
      IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun g hg i =>
    (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hg
  have hslln : ∀ (g : 𝓧 → ℝ), Measurable g → Integrable g μX →
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g (X i ω)) / n) atTop
        (𝓝 (∫ x, g x ∂μX)) := fun g hg hgi => by
    have h := strong_law_ae_real (fun i => g ∘ X i) ((hX_law 0).integrable_comp hgi)
      (fun i j hij => (hX_indep.comp (fun _ => g) (fun _ => hg)).indepFun hij) (hident g hg)
    rwa [(hX_law 0).integral_comp hg.aestronglyMeasurable] at h
  -- CLT for `A`
  have hvar_nonneg : 0 ≤ (∫ x, ψ θ₀ x ^ 2 ∂μX) / (∫ x, ψ' x ∂μX) ^ 2 :=
    div_nonneg (integral_nonneg fun x => sq_nonneg _) (sq_nonneg _)
  have hA : TendstoInDistribution A atTop (fun ω => J * Y ω) (fun _ => P) P' := by
    set Z : ℕ → Ω → ℝ := fun i => ψ θ₀ ∘ X i
    have hmean : P[Z 0] = 0 := by
      rw [← hψ_mean]; exact (hX_law 0).integral_comp hψ_meas.aestronglyMeasurable
    have hL2 : MemLp (Z 0) 2 P := (hX_law 0).memLp_comp
      ((memLp_two_iff_integrable_sq hψ_meas.aestronglyMeasurable).2 hψ_sq)
    have hsq : P[fun ω => Z 0 ω ^ 2] = ∫ x, ψ θ₀ x ^ 2 ∂μX :=
      (hX_law 0).integral_comp (f := fun x => ψ θ₀ x ^ 2)
        (hψ_meas.pow_const 2).aestronglyMeasurable
    have hvar : Var[Z 0; P] = ∫ x, ψ θ₀ x ^ 2 ∂μX := by
      rw [variance_of_integral_eq_zero hL2.aemeasurable hmean]; exact hsq
    have hJY : HasLaw (fun ω => J * Y ω) (gaussianReal 0 Var[Z 0; P].toNNReal) P' := by
      have h := gaussianReal_const_mul hY J
      rw [mul_zero] at h
      convert h using 2
      ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hvar_nonneg, hvar,
        Real.coe_toNNReal _ (integral_nonneg fun x => sq_nonneg (ψ θ₀ x)), hJ_def, neg_sq]
      field_simp
    have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hJY hL2
      (hX_indep.comp (fun _ => ψ θ₀) (fun _ => hψ_meas)) (hident _ hψ_meas)
    have hmean' : ∫ ω, ψ θ₀ (X 0 ω) ∂P = 0 := hmean
    simpa [hmean', Z] using h
  -- laws of large numbers
  have hB : TendstoInMeasure P B atTop (fun _ => J) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hB_meas n).aestronglyMeasurable) ?_
    filter_upwards [hslln _ hψ'_meas hψ'_int] with ω hω
    exact hω.neg
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M x ∂μX) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable)
      (hslln _ hM_meas hM_int)
  have hBJ : TendstoInMeasure P (fun n ω => |B n ω - J|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀| * Mb n ω) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ
      (fun n => continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _))
    simpa only [mul_comm] using h
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero hBJ hrem
  -- the good events
  set G : ℕ → Set Ω := fun n => {ω | ∑ i ∈ Finset.range n, ψ (θhat n ω) (X i ω) = 0} ∩
    {ω | |θhat n ω - θ₀| < δ} ∩ {ω | η n ω ≤ |J| / 2} with hG_def
  have hJpos : 0 < |J| := abs_pos.2 hJ0
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h2 := (tendstoInMeasure_iff_norm.1 hη) (|J| / 2) (by positivity)
    have h3 := (hroot.add h1).add h2
    simp only [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => ?_
    refine (measure_mono fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt, not_le] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, Pi.zero_apply, sub_zero,
      Real.norm_eq_abs]
    rcases hω with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (h.le.trans (le_abs_self _))
  -- the deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n,
      |T n ω - A n ω / J| ≤ (2 / J ^ 2 * |A n ω|) * η n ω := by
    intro n ω hω
    obtain ⟨⟨hroot', hclose⟩, hsmall⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose hsmall
    set d := θhat n ω - θ₀
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]; exact hclose
    -- summed Taylor bound
    have htay : |∑ i ∈ Finset.range n, ψ θ₀ (X i ω) + d * ∑ i ∈ Finset.range n, ψ' (X i ω)|
        ≤ (∑ i ∈ Finset.range n, M (X i ω)) * d ^ 2 := by
      have e : ∑ i ∈ Finset.range n, ψ θ₀ (X i ω) + d * ∑ i ∈ Finset.range n, ψ' (X i ω) =
          -∑ i ∈ Finset.range n, (ψ (θhat n ω) (X i ω) - ψ θ₀ (X i ω) - d * ψ' (X i ω)) := by
        simp only [Finset.sum_sub_distrib, hroot', Finset.mul_sum]; ring
      rw [e, abs_neg, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact abs_sub_sub_mul_deriv_le (f := fun t => ψ t (X i ω)) (hψ_diff (X i ω))
        (hψ'_diff (X i ω))
        (hM (X i ω)) hball
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT_def, hA_def]
    have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hrr : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hMb0 : 0 ≤ Mb n ω := div_nonneg (Finset.sum_nonneg fun i _ => hM0 _) (Nat.cast_nonneg n)
    -- `|A - T B| ≤ |T| |d| Mb`
    have hATB : |A n ω - T n ω * B n ω| ≤ |T n ω| * (|d| * Mb n ω) := by
      have e1 : A n ω - T n ω * B n ω = (∑ i ∈ Finset.range n, ψ θ₀ (X i ω) +
          d * ∑ i ∈ Finset.range n, ψ' (X i ω)) / √(n : ℝ) := by
        simp only [hA_def, hT_def, hB_def]
        obtain ⟨r, hr_def⟩ : ∃ r, r = √(n : ℝ) := ⟨_, rfl⟩
        have hn' : (n : ℝ) = r ^ 2 := by rw [hr_def, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [← hr_def] at hr ⊢
        rw [hn']
        field_simp
        ring
      have e2 : |T n ω| * (|d| * Mb n ω) =
          (∑ i ∈ Finset.range n, M (X i ω)) * d ^ 2 / √(n : ℝ) := by
        simp only [hT_def, hMb_def, abs_mul, abs_of_pos hr]
        obtain ⟨r, hr_def⟩ : ∃ r, r = √(n : ℝ) := ⟨_, rfl⟩
        have hn' : (n : ℝ) = r ^ 2 := by rw [hr_def, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [← hr_def] at hr ⊢
        rw [hn', ← sq_abs d]
        field_simp
        ring
      rw [e1, e2, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right htay hr.le
    have hATJ : |A n ω - T n ω * J| ≤ |T n ω| * η n ω := by
      have : A n ω - T n ω * J = (A n ω - T n ω * B n ω) + T n ω * (B n ω - J) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, hη_def]
      simp only
      nlinarith [abs_nonneg (T n ω), abs_nonneg (B n ω - J)]
    have hη0 : 0 ≤ η n ω := add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMb0)
    have hTle : |T n ω| * |J| ≤ 2 * |A n ω| := by
      have h1 : |T n ω * J| ≤ |A n ω| + |A n ω - T n ω * J| := by
        have := abs_sub_abs_le_abs_sub (T n ω * J) (A n ω)
        rw [abs_sub_comm (T n ω * J)] at this
        linarith
      rw [abs_mul] at h1
      nlinarith [abs_nonneg (T n ω)]
    have e : T n ω - A n ω / J = -(A n ω - T n ω * J) / J := by field_simp; ring
    rw [e, abs_div, abs_neg, div_le_iff₀ hJpos]
    have hJ2 : J ^ 2 = |J| * |J| := by rw [← sq_abs, sq]
    calc |A n ω - T n ω * J| ≤ |T n ω| * η n ω := hATJ
      _ ≤ 2 / J ^ 2 * |A n ω| * η n ω * |J| := by
        rw [hJ2]
        have : |T n ω| ≤ 2 * |A n ω| / |J| := by rw [le_div_iff₀ hJpos]; exact hTle
        calc |T n ω| * η n ω ≤ 2 * |A n ω| / |J| * η n ω :=
              mul_le_mul_of_nonneg_right this hη0
          _ = 2 / (|J| * |J|) * |A n ω| * η n ω * |J| := by field_simp
  -- `(2 / J²) |A| η → 0` in probability
  have hV : TendstoInMeasure P (fun n ω => (2 / J ^ 2 * |A n ω|) * η n ω) atTop 0 := by
    have hA' := hA.continuous_comp (g := fun x => 2 / J ^ 2 * |x|) (by fun_prop)
    exact hA'.mul_tendstoInMeasure_zero hη hη_meas
  have hdiff : TendstoInMeasure P (fun n ω => T n ω - A n ω / J) atTop 0 :=
    tendstoInMeasure_zero_of_abs_le hV hG hbound
  -- conclusion
  have hAJ : TendstoInDistribution (fun n ω => A n ω / J) atTop Y (fun _ => P) P' := by
    have h := hA.continuous_comp (g := fun x => x / J) (by fun_prop)
    refine h.congr (fun n => ae_of_all _ fun ω => rfl) (ae_of_all _ fun ω => ?_)
    simp [Function.comp, mul_div_cancel_left₀ _ hJ0]
  exact tendstoInDistribution_of_tendstoInMeasure_sub (fun n ω => T n ω) Y hAJ hdiff hT_meas

/-- **Asymptotic normality of maximum likelihood** (Cramér's conditions). Let `p θ` be positive
densities with respect to `ν`, measurable at `θ₀`, and let `X 0, X 1, …` be i.i.d. with law
`p θ₀ ν`. Assume that on the ball of radius `δ > 0` about `θ₀` the log-likelihood
`log p θ x` is differentiable in `θ` for every `x` (so that `score p θ x` is its true derivative
there, not Lean's junk value `0` of `deriv` at a nondifferentiable point) and the score
`∂_θ log p θ x` is twice differentiable in `θ` for every `x`, with `|∂³_θ log p θ x| ≤ M x`
for an integrable `M`; that the score `∂_θ log p θ₀` is measurable and square integrable with
mean zero; that `∂²_θ log p θ₀` is measurable and integrable with `E ∂²_θ log p θ₀ = -I(θ₀)`
(the information identity); and that `0 < I(θ₀)`. The two moment identities are what
differentiating `∫ p θ dν = 1` twice under the integral sign gives; they are assumed directly.
Let `θhat n` be estimators that solve the likelihood equation `∑_{i<n} ∂_θ log p θ (X i) = 0`
with probability tending to one and converge to `θ₀` in probability. Then
`√n (θhat n - θ₀) → N(0, 1 / I(θ₀))` in distribution.

Source: Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.3.10; van der Vaart (1998),
Theorem 5.41. -/
theorem tendstoInDistribution_sqrt_mul_sub_maximumLikelihood
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (p θ₀))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (fisherInformation ν p θ₀)⁻¹.toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (θhat n ω - θ₀)) atTop Y (fun _ => P) P' := by
  have hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀ := fun x => by
    have e : (fun t => p t x) = fun t => Real.exp (Real.log (p t x)) := by
      funext t; rw [Real.exp_log (hp_pos t x)]
    rw [e]; exact (hℓ_diff x θ₀ (Metric.mem_ball_self hδ)).exp
  have hvar : (∫ x, score p θ₀ x ^ 2 ∂lawOf ν p θ₀) /
      (∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀) ^ 2 = (fisherInformation ν p θ₀)⁻¹ := by
    rw [integral_score_sq (hp_pos θ₀) hp_meas hp_diff, h_info, neg_sq, sq, div_mul_cancel_left₀
      hI_pos.ne']
  refine tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation hX_law hX_indep hδ hs_diff
    hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int
    (by rw [h_info]; exact neg_ne_zero.2 hI_pos.ne') hθ_meas hroot hcons ?_
  rwa [hvar]

end MathlibExt.Probability.Statistics.MLEAsymptoticNormality
