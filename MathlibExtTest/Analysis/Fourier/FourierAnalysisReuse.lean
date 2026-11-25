/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance

/-!
Canonical mathlib APIs for the archived `v1/Atlas/FourierAnalysis` targets that mathlib
already proves. Each example states mathlib's form of a target, numbered by its zero-based
ordinal in `v1/Atlas/FourierAnalysis/targets.yaml`. mathlib's Fourier transform is
`∫ e^{-2πi⟨x, ξ⟩} f(x) dx`, while the book's is `∫ e^{-ixξ} f(x) dx` with `1/2π` in the
inverse; the two differ by the dilation `ξ ↦ ξ / 2π`
(`MathlibExt/Analysis/Fourier/Scaling.lean`), so targets 6 and 7 are checked in
mathlib's normalization. mathlib's `charFun μ ξ = ∫ e^{ixξ} dμ` is the book's `μ̂(-ξ)`, which
does not affect target 18's hypothesis "for each `ξ`". mathlib states Lévy's continuity
theorem for probability measures; target 18 is about finite positive measures, so its example
reduces to that case by normalizing the total masses. Target 19 is not checked here: its
hypothesis, convergence against smooth compactly supported functions for finite measures, is
weaker than the weak convergence mathlib's portmanteau theorem assumes. These are
canonical-use checks, not verification against the printed textbook.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory AddCircle
open scoped SchwartzMap FourierTransform ENNReal

section FourierSeries

variable {T : ℝ} [hT : Fact (0 < T)]

-- Target 3: trigonometric polynomials are dense in `C(𝕋)`.
example : (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure = ⊤ :=
  span_fourier_closure_eq_top

-- Target 4: the characters form a Hilbert basis of `L²(𝕋)`, the partial sums
-- converge in `L²`, and Parseval's identity holds.
example : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _ := coe_fourierBasis

example (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f :=
  hasSum_fourier_series_L2 f

example (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle :=
  tsum_sq_fourierCoeff f

end FourierSeries

section FourierIntegrals

-- Target 6: Fourier inversion on `𝓢(ℝ)`.
example (f : 𝓢(ℝ, ℂ)) : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f

-- Target 7: Plancherel on `𝓢(ℝ)` (mathlib's normalization has no `2π` factor).
example (f : 𝓢(ℝ, ℂ)) : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f

-- Target 22: the inverse Fourier transform inverts the Fourier transform on `𝓢'(ℝ)`.
example (T : 𝓢'(ℝ, ℂ)) : 𝓕 (𝓕⁻ T) = T := FourierTransform.fourier_fourierInv_eq T

end FourierIntegrals

section Measures

-- Target 17: a finite measure on `ℝ` is determined by its Fourier transform.
example {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFun μ = charFun ν) :
    μ = ν :=
  Measure.ext_of_charFun h

-- Target 18: for finite positive measures, pointwise convergence of the Fourier transforms
-- implies convergence of the integrals of every Schwartz function. The total masses converge
-- (`charFun μ 0 = μ ℝ`); a zero limit mass is handled by `‖∫ f dμ‖ ≤ ‖f‖∞ μ ℝ`, and otherwise
-- mathlib's Lévy theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) applies to the
-- normalized measures, which together with the masses gives weak convergence.
example (μ : ℕ → Measure ℝ) (μ₀ : Measure ℝ) [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure μ₀]
    (h : ∀ ξ : ℝ, Tendsto (fun j ↦ charFun (μ j) ξ) atTop (𝓝 (charFun μ₀ ξ)))
    (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun j ↦ ∫ x, f x ∂(μ j)) atTop (𝓝 (∫ x, f x ∂μ₀)) := by
  have hmass : Tendsto (fun j ↦ (μ j).real Set.univ) atTop (𝓝 (μ₀.real Set.univ)) := by
    simpa [Function.comp_def, charFun_zero] using (Complex.continuous_re.tendsto _).comp (h 0)
  by_cases h0 : μ₀ = 0
  · subst h0
    simp only [integral_zero_measure]
    have hb : ∀ j, ‖∫ x, f x ∂(μ j)‖ ≤ ‖f.toBoundedContinuousFunction‖ * (μ j).real Set.univ :=
      fun j ↦ norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm x)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun j ↦ norm_nonneg _) hb ?_
    simpa using hmass.const_mul ‖f.toBoundedContinuousFunction‖
  · let F : ℕ → FiniteMeasure ℝ := fun j ↦ ⟨μ j, inferInstance⟩
    let F₀ : FiniteMeasure ℝ := ⟨μ₀, inferInstance⟩
    have hF₀ : F₀ ≠ 0 := fun h ↦ h0 (congrArg (fun ν : FiniteMeasure ℝ ↦ (ν : Measure ℝ)) h)
    have hcoe : ∀ ν : FiniteMeasure ℝ, (ν.mass : ℝ) = (ν : Measure ℝ).real Set.univ := fun ν ↦ by
      rw [measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
    have hmassF : Tendsto (fun j ↦ (F j).mass) atTop (𝓝 F₀.mass) := by
      rw [← NNReal.tendsto_coe]
      simp only [hcoe]
      exact hmass
    have key : ∀ ν : FiniteMeasure ℝ, ν ≠ 0 → ∀ t, charFun (ν.normalize : Measure ℝ) t =
        ((ν.mass : ℝ) : ℂ)⁻¹ * charFun (ν : Measure ℝ) t := by
      intro ν hν t
      rw [ν.toMeasure_normalize_eq_of_nonzero hν, charFun_apply, charFun_apply,
        integral_smul_nnreal_measure]
      simp [NNReal.smul_def, Complex.real_smul]
    have hpos : (F₀.mass : ℝ) ≠ 0 := by
      simpa using (FiniteMeasure.mass_nonzero_iff F₀).2 hF₀
    have hev : ∀ᶠ j in atTop, F j ≠ 0 := by
      have := (NNReal.tendsto_coe.2 hmassF).eventually_ne hpos
      filter_upwards [this] with j hj hF
      exact hj (by simp [hF])
    have hnorm : Tendsto (fun j ↦ (F j).normalize) atTop (𝓝 F₀.normalize) := by
      refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
      rw [key F₀ hF₀]
      refine Tendsto.congr' (hev.mono fun j hj ↦ (key (F j) hj t).symm) ?_
      refine Tendsto.mul ?_ (h t)
      refine ((Complex.continuous_ofReal.tendsto _).comp (NNReal.tendsto_coe.2 hmassF)).inv₀ ?_
      exact_mod_cast hpos
    have hlim : Tendsto F atTop (𝓝 F₀) :=
      (FiniteMeasure.tendsto_normalize_iff_tendsto hF₀).1 ⟨hnorm, hmassF⟩
    simpa [F, F₀] using (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hlim
      f.toBoundedContinuousFunction

-- Target 20 (central limit theorem); mathlib needs only a finite second moment.
example {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

end Measures

section HilbertSpaces

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- Target 23: the norm is continuous and the inner product is jointly continuous.
example {u : ℕ → E} {a : E} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖a‖) :=
  hu.norm

example {u v : ℕ → E} {a b : E} (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => inner 𝕜 (u n) (v n)) atTop (𝓝 (inner 𝕜 a b)) :=
  hu.inner hv

-- Target 24: an orthonormal sequence is mathlib's `Orthonormal`: `⟪φ n, φ m⟫ = 0` for `n ≠ m`
-- and `⟪φ n, φ n⟫ = ‖φ n‖ ^ 2 = 1`.
example (φ : ℕ → E) :
    Orthonormal 𝕜 φ ↔ ∀ n m, inner 𝕜 (φ n) (φ m) = if n = m then 1 else 0 :=
  orthonormal_iff_ite

example (φ : ℕ → E) (h : Orthonormal 𝕜 φ) (n : ℕ) : ‖φ n‖ = 1 :=
  h.norm_eq_one n

-- Target 26: `Lᵖ` is complete for `1 ≤ p`.
example {X F : Type*} [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup F] [CompleteSpace F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : CompleteSpace (Lp F p μ) :=
  inferInstance

-- Target 28: smooth compactly supported functions are dense in `Lᵖ(ℝⁿ)`, `1 ≤ p < ∞`.
example (n : ℕ) {p : ℝ≥0∞} (hp : p ≠ ⊤) [Fact (1 ≤ p)] :
    Dense {f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n))) |
      ∃ g : EuclideanSpace ℝ (Fin n) → ℂ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧
        ContDiff ℝ (⊤ : ℕ∞) g} :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp

end HilbertSpaces

section BrownianMotion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : NNReal → Ω → ℝ}

-- Target 33: a process with independent increments `B t - B s ~ 𝓝(0, t - s)` and `B 0 = 0`
-- almost surely (property (2), mathlib's `IsPreBrownianReal`) is exactly (a) a centred Gaussian
-- process (`IsGaussianProcess`: every finite family `(B t₁, …, B tₘ)`, hence every combination
-- `∑ ξⱼ B tⱼ`, is Gaussian) with (b) `𝔼[B s B t] = min s t`. mathlib's converse needs neither
-- `B 0 = 0` nor the increments: (b) gives `Var[B 0] = 0`.
example (hB : IsPreBrownianReal B P) :
    IsGaussianProcess B P ∧ (∀ t, P[B t] = 0) ∧ ∀ s t, ∫ ω, B s ω * B t ω ∂P = min s t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨hB.isGaussianProcess, hB.integral_eval, fun s t ↦ ?_⟩
  have h := hB.covariance_eval s t
  rw [covariance_eq_sub (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two, hB.integral_eval,
    hB.integral_eval] at h
  simpa using h

example (hG : IsGaussianProcess B P) (hmean : ∀ t, P[B t] = 0)
    (hcov : ∀ s t, ∫ ω, B s ω * B t ω ∂P = min s t) : IsPreBrownianReal B P := by
  have := hG.isProbabilityMeasure
  refine hG.isPreBrownianReal_of_covariance hmean fun s t hst ↦ ?_
  rw [covariance_eq_sub (hG.hasGaussianLaw_eval s).memLp_two (hG.hasGaussianLaw_eval t).memLp_two,
    hmean, hmean]
  simpa [min_eq_left hst] using hcov s t

-- Target 33, in increments: pre-Brownian motion has independent increments, and independent
-- increments with `B t ~ 𝓝(0, t)` give a pre-Brownian motion.
example (hB : IsPreBrownianReal B P) : HasIndepIncrements B P := hB.hasIndepIncrements

example (law : ∀ t, HasLaw (B t) (gaussianReal 0 t) P) (incr : HasIndepIncrements B P) :
    IsPreBrownianReal B P :=
  incr.isPreBrownianReal_of_hasLaw law

end BrownianMotion

#print axioms span_fourier_closure_eq_top
#print axioms coe_fourierBasis
#print axioms hasSum_fourier_series_L2
#print axioms tsum_sq_fourierCoeff
#print axioms SchwartzMap.integral_norm_sq_fourier
#print axioms Measure.ext_of_charFun
#print axioms ProbabilityMeasure.tendsto_iff_tendsto_charFun
#print axioms FiniteMeasure.tendsto_normalize_iff_tendsto
#print axioms FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto
#print axioms tendstoInDistribution_inv_sqrt_mul_sum_sub
#print axioms Filter.Tendsto.norm
#print axioms Filter.Tendsto.inner
#print axioms orthonormal_iff_ite
#print axioms Orthonormal.norm_eq_one
#print axioms MeasureTheory.Lp.dense_hasCompactSupport_contDiff
#print axioms IsPreBrownianReal.isGaussianProcess
#print axioms IsPreBrownianReal.integral_eval
#print axioms IsPreBrownianReal.covariance_eval
#print axioms IsGaussianProcess.isPreBrownianReal_of_covariance
#print axioms IsPreBrownianReal.hasIndepIncrements
#print axioms HasIndepIncrements.isPreBrownianReal_of_hasLaw

end
