/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Score-based diffusion models: forward process and DDPM sampler

This file sets up the objects in the sampling guarantee for denoising diffusion probabilistic
models (DDPM) of S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy
as learning the score: theory for diffusion models with minimal data assumptions*,
arXiv:2209.11215v3, Sections 2.1 and 3.1, on a finite-dimensional real inner product space `E`.
All objects are laws, given by the source's closed forms.

* `ouMarginal q t`: the law at time `t` of the Ornstein–Uhlenbeck process `dX = -X dt + √2 dB`
  started from `q`, given by the source's closed form: the law of `e^{-t} X₀ + √(1 - e^{-2t}) Z`
  with `X₀ ∼ q` and `Z` an independent standard Gaussian vector (`ProbabilityTheory.stdGaussian`).
* `logDensityScore ρ`: the score `∇ log ρ` of a density `ρ`, through Mathlib's `gradient` (which
  is `0` where the function is not differentiable).
* `ddpmStep h σ μ`: one sampler step with the score value frozen at the start of the step, given
  by the closed-form solution `e^h x + 2 (e^h - 1) σ x + √(e^{2h} - 1) ξ` of the source's
  equation (2.8) over a step of length `h`.
* `ddpmLaw h s N j`: the law after `j` steps, started at the standard Gaussian; step `j + 1` uses
  the estimate `s (N - j)` of the score at time `(N - j) h`, so an `N`-step run uses
  `s N, …, s 1` and never `s 0`. `ddpmOutput h s N` is the output law `p_T`, `T = N h`.

## Main results

* `ouMarginal_zero`: the forward process starts at the data law.
* `ouMarginal_stdGaussian`: the standard Gaussian is stationary for the forward process.
* `ddpmOutput_one`, `ddpmOutput_congr`: a one-step run is one step from the standard Gaussian,
  and the output depends only on the estimates `s 1, …, s N`.
* Probability instances: `isProbabilityMeasure_ouMarginal`, `isProbabilityMeasure_ddpmStep`,
  `isProbabilityMeasure_ddpmLaw`, `isProbabilityMeasure_ddpmOutput`.

## Non-claims

This file does not claim: the sampling guarantee (Theorem 2 of the source); the identification of
`ouMarginal` or `ddpmStep` with solutions of the stochastic differential equations (2.1) and (2.8)
of the source; existence or the law of the time reversal (2.4); the equivalence of score matching
objectives (2.5) and (2.6); the time-rescaled process (2.2); Theorem 1, Corollaries 3-5, Theorems
6, 7, 9 and 15, or Lemmas 10 and 11 of the source.
-/

@[expose] public section

namespace Cslib.MachineLearning.ScoreDiffusion

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- **Forward Ornstein–Uhlenbeck marginal.** The law at time `t` of the Ornstein–Uhlenbeck process
`dX = -X dt + √2 dB` started from `q`: the law of `e^{-t} X₀ + √(1 - e^{-2t}) Z` with `X₀ ∼ q` and
`Z` an independent standard Gaussian vector (Chen et al., arXiv:2209.11215v3, Section 2.1). Only
times `t ≥ 0` are meaningful: for `t < 0`, `1 - e^{-2t}` is negative and its `Real.sqrt` is `0`. -/
noncomputable def ouMarginal (q : Measure E) (t : ℝ) : Measure E :=
  (q.prod (stdGaussian E)).map
    fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2

/-- **Score of a density.** The score `∇ log ρ` of a density `ρ`, through Mathlib's `gradient`
(`0` at points where `log ∘ ρ` is not differentiable). The gradient is taken in the space variable,
as in score matching; `MathlibExt.Probability.Statistics.VectorInference.score` is instead the
gradient `∇_θ log p θ x` in the parameter of a statistical model. -/
noncomputable def logDensityScore (ρ : E → ℝ) : E → E :=
  gradient fun x => Real.log (ρ x)

/-- **DDPM sampler step.** One step of the DDPM sampler with the score value frozen at the start
of the step: the law of `e^h x + 2 (e^h - 1) σ x + √(e^{2h} - 1) ξ` for `x ∼ μ` and an independent
standard Gaussian `ξ`, the closed-form solution of equation (2.8) of Chen et al.
(arXiv:2209.11215v3) over one step. If the update map is not a.e.-measurable, `Measure.map` falls
back to a Dirac mass. Only steps `h ≥ 0` are meaningful: for `h < 0`, `e^{2h} - 1` is negative and
its `Real.sqrt` is `0`. -/
noncomputable def ddpmStep (h : ℝ) (σ : E → E) (μ : Measure E) : Measure E :=
  (μ.prod (stdGaussian E)).map fun p =>
    Real.exp h • p.1 + (2 * (Real.exp h - 1)) • σ p.1 + Real.sqrt (Real.exp (2 * h) - 1) • p.2

/-- **DDPM sampler laws.** The laws of the DDPM sampler with step `h` and `N` steps, started at
the standard Gaussian; `s k` estimates the score at time `k h`, and step `j + 1` uses `s (N - j)`.
Only `j ≤ N` is meaningful: with natural subtraction, the steps after the `N`-th use `s 0`. -/
noncomputable def ddpmLaw (h : ℝ) (s : ℕ → E → E) (N : ℕ) : ℕ → Measure E
  | 0 => stdGaussian E
  | j + 1 => ddpmStep h (s (N - j)) (ddpmLaw h s N j)

/-- **DDPM output law.** The output law `p_T` of the DDPM sampler with step `h` and `N` steps,
`T = N h`. -/
noncomputable def ddpmOutput (h : ℝ) (s : ℕ → E → E) (N : ℕ) : Measure E :=
  ddpmLaw h s N N

/-- **Forward process at time zero.** The forward process starts at the data law. -/
@[simp]
theorem ouMarginal_zero (q : Measure E) : ouMarginal q 0 = q := by
  simp [ouMarginal]

/-- **Stationarity of the standard Gaussian.** The standard Gaussian is stationary for the forward
Ornstein–Uhlenbeck process. -/
theorem ouMarginal_stdGaussian [BorelSpace E] {t : ℝ} (ht : 0 ≤ t) :
    ouMarginal (stdGaussian E) t = stdGaussian E := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-2 * t))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have h1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    simp only [a, b, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-2 * t))]
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hconv : ouMarginal (stdGaussian E) t =
      (stdGaussian E).map (a • ·) ∗ (stdGaussian E).map (b • ·) := by
    rw [ouMarginal, Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hconv]
  refine Measure.ext_of_charFun (funext fun u => ?_)
  rw [charFun_conv, charFun_map_smul, charFun_map_smul, charFun_stdGaussian,
    charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hr : (‖a‖ * ‖u‖) ^ 2 + (‖b‖ * ‖u‖) ^ 2 = ‖u‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    linear_combination ‖u‖ ^ 2 * hab
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  push_cast at hc
  rw [norm_smul, norm_smul]
  push_cast
  linear_combination (-1 / 2 : ℂ) * hc

@[simp]
theorem ddpmLaw_zero (h : ℝ) (s : ℕ → E → E) (N : ℕ) : ddpmLaw h s N 0 = stdGaussian E :=
  rfl

theorem ddpmLaw_succ (h : ℝ) (s : ℕ → E → E) (N j : ℕ) :
    ddpmLaw h s N (j + 1) = ddpmStep h (s (N - j)) (ddpmLaw h s N j) :=
  rfl

/-- **One-step DDPM run.** A one-step run is one step from the standard Gaussian with the estimate
at time `h`. -/
theorem ddpmOutput_one (h : ℝ) (s : ℕ → E → E) :
    ddpmOutput h s 1 = ddpmStep h (s 1) (stdGaussian E) :=
  rfl

/-- **Estimates the DDPM output depends on.** The output of an `N`-step run depends only on the
estimates `s 1, …, s N`; in particular it does not use `s 0`. -/
theorem ddpmOutput_congr (h : ℝ) {s s' : ℕ → E → E} {N : ℕ}
    (hs : ∀ k ∈ Finset.Icc 1 N, s k = s' k) : ddpmOutput h s N = ddpmOutput h s' N := by
  suffices key : ∀ j ≤ N, ddpmLaw h s N j = ddpmLaw h s' N j from key N le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ddpmLaw_succ, ddpmLaw_succ, ih (by omega),
      hs (N - j) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]

/-- The forward marginal of a probability law is a probability law. -/
instance isProbabilityMeasure_ouMarginal (q : Measure E)
    [IsProbabilityMeasure q] (t : ℝ) : IsProbabilityMeasure (ouMarginal q t) := by
  unfold ouMarginal
  infer_instance

/-- One sampler step from a probability law is a probability law. -/
instance isProbabilityMeasure_ddpmStep (h : ℝ) (σ : E → E) (μ : Measure E)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (ddpmStep h σ μ) := by
  unfold ddpmStep
  infer_instance

/-- Every sampler law is a probability law. -/
instance isProbabilityMeasure_ddpmLaw (h : ℝ) (s : ℕ → E → E) (N j : ℕ) :
    IsProbabilityMeasure (ddpmLaw h s N j) := by
  induction j with
  | zero =>
    rw [ddpmLaw_zero]
    infer_instance
  | succ j ih =>
    rw [ddpmLaw_succ]
    infer_instance

/-- The sampler output law is a probability law. -/
instance isProbabilityMeasure_ddpmOutput (h : ℝ) (s : ℕ → E → E) (N : ℕ) :
    IsProbabilityMeasure (ddpmOutput h s N) := by
  unfold ddpmOutput
  infer_instance

end Cslib.MachineLearning.ScoreDiffusion
