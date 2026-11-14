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
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.CentralLimitTheorem

/-!
Canonical mathlib APIs for the archived `v1/Atlas/FourierAnalysis` targets that mathlib
already proves. Each example states mathlib's form of a target, numbered by its zero-based
ordinal in `v1/Atlas/FourierAnalysis/targets.yaml`. mathlib's Fourier transform is
`∫ e^{-2πi⟨x, ξ⟩} f(x) dx`, while the book's is `∫ e^{-ixξ} f(x) dx` with `1/2π` in the
inverse; the two differ by the dilation `ξ ↦ ξ / 2π`
(`MathlibExt/Analysis/Fourier/Scaling.lean`), so targets 6 and 7 are checked in
mathlib's normalization. Measures are probability measures where mathlib states the
result for them, and target 19's smooth test functions become mathlib's weak
convergence. These are canonical-use checks, not verification against the printed
textbook.
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

-- Target 18 (Lévy): pointwise convergence of Fourier transforms is weak convergence.
example (μ : ℕ → ProbabilityMeasure ℝ) (μ₀ : ProbabilityMeasure ℝ) :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop (𝓝 (charFun (μ₀ : Measure ℝ) t)) :=
  ProbabilityMeasure.tendsto_iff_tendsto_charFun

-- Target 19: under weak convergence, `μ_j (a, b) → μ (a, b)` when `μ` has no atoms at `a, b`.
example (μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ) (h : Tendsto μs atTop (𝓝 μ))
    {a b : ℝ} (hab : (μ : Measure ℝ) (frontier (Set.Ioo a b)) = 0) :
    Tendsto (fun j ↦ (μs j : Measure ℝ) (Set.Ioo a b)) atTop (𝓝 ((μ : Measure ℝ) (Set.Ioo a b))) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hab

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

-- Target 23: the inner product is jointly continuous.
example {u v : ℕ → E} {a b : E} (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => inner 𝕜 (u n) (v n)) atTop (𝓝 (inner 𝕜 a b)) :=
  hu.inner hv

-- Target 24: an orthonormal sequence is mathlib's `Orthonormal`.
example (φ : ℕ → E) (h : Orthonormal 𝕜 φ) (n m : ℕ) (hnm : n ≠ m) : inner 𝕜 (φ n) (φ m) = 0 :=
  h.inner_eq_zero hnm

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

-- Target 33: Brownian motion has independent Gaussian increments, and conversely
-- independent increments with `B t ~ N(0, t)` give a (pre-)Brownian motion.
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
#print axioms ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
#print axioms tendstoInDistribution_inv_sqrt_mul_sum_sub
#print axioms Filter.Tendsto.inner
#print axioms MeasureTheory.Lp.dense_hasCompactSupport_contDiff
#print axioms IsPreBrownianReal.hasIndepIncrements
#print axioms HasIndepIncrements.isPreBrownianReal_of_hasLaw

end
