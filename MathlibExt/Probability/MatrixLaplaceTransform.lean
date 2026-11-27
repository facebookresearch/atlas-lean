/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.HermitianTraceExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The matrix Laplace transform method

Let `Y` be a random Hermitian `d × d` matrix. The matrix Laplace transform method controls the
extreme eigenvalues of `Y` by the trace of the matrix moment generating function
`θ ↦ E tr e^{θY}` (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
Found. Trends Mach. Learn. 8 (2015), arXiv:1501.01571, §3.2; J. A. Tropp, *User-friendly tail
bounds for sums of random matrices*, Found. Comput. Math. 12 (2012), Proposition 3.1. A version
of the method is due to R. Ahlswede and A. Winter (2002); the statement in this form is from
R. I. Oliveira (2010), see Tropp's §3.7.1):

* **tail bounds** (Proposition 3.2.1): for every `t` and every `θ > 0`,
  `P{λmax(Y) ≥ t} ≤ e^{-θt} E tr e^{θY}`, and for every `θ < 0`,
  `P{λmin(Y) ≤ t} ≤ e^{-θt} E tr e^{θY}`. Since the bound holds for each `θ`, it holds for the
  infimum over `θ`, which is how Tropp states it;
* **expectation bound** (Proposition 3.2.2, display (3.2.4)): for every `θ > 0`,
  `E λmax(Y) ≤ θ⁻¹ log E tr e^{θY}`.

The proof is the scalar Laplace transform argument (Markov's inequality applied to
`e^{θ λmax(Y)}`, respectively Jensen's inequality for the exponential) followed by the matrix
step `e^{θ λmax(Y)} ≤ tr e^{θY}` (`Matrix.IsHermitian.exp_mul_lambdaMax_le_re_trace_exp`).
Here `e^{θY}` is the power-series matrix exponential and `tr` is the real part of the trace.

The integrability hypotheses are explicit: without them the Bochner integral is `0` and the
bounds would be false.

The file also defines the entrywise expectation `expect` of a random matrix and the matrix
Gaussian series `gaussianSeries`, the objects in which the matrix Chernoff, Bernstein, Hoeffding
and Gaussian-series inequalities are stated (`MathlibExt.Probability.MatrixConcentrationWanted`).
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.MatrixLaplaceTransform

variable {Ω n 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [Nonempty n]

/-- **Expectation of a random matrix.** The entrywise expectation `E M` of a random matrix
`M : Ω → Matrix n n 𝕜` under a probability measure `μ` (Tropp, arXiv:1501.01571, §2.2.4). For
another measure the entrywise integral is not an expectation: under the zero measure every
random matrix, the identity included, would have expectation `0`. -/
noncomputable def expect (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → Matrix n n 𝕜) :
    Matrix n n 𝕜 :=
  Matrix.of fun i j => ∫ ω, M ω i j ∂μ

/-- **Matrix Gaussian series.** For fixed matrices `A₀, …, A_{N-1}` and a vector `ω ∈ ℝᴺ` of
coefficients, the matrix `∑ₖ ωₖ Aₖ`; with `ω` standard Gaussian this is the matrix Gaussian series
`Y = ∑ₖ γₖ Aₖ` of Tropp, arXiv:1501.01571, §4.1 and §4.6. -/
noncomputable def gaussianSeries {N : ℕ} (A : Fin N → Matrix n n 𝕜) (ω : Fin N → ℝ) :
    Matrix n n 𝕜 :=
  ∑ k, ((ω k : ℝ) : 𝕜) • A k

/-- **Trace moment generating function.** For a random matrix `Y` and a real `θ`, the real
number `tr e^{θ Y(ω)}` (the real part of the trace); its expectation `E tr e^{θY}` is the trace
mgf of Tropp, arXiv:1501.01571, §3.2. -/
noncomputable def traceMgf (Y : Ω → Matrix n n 𝕜) (θ : ℝ) (ω : Ω) : ℝ :=
  RCLike.re (NormedSpace.exp (θ • Y ω)).trace

/-- **Matrix Laplace transform method, upper tail** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Proposition 3.2.1, display (3.2.1)). Let `Y` be
a random Hermitian matrix on a finite measure space, and let `θ > 0` be such that
`ω ↦ tr e^{θY(ω)}` is integrable. Then for every real `t`,
`μ{λmax(Y) ≥ t} ≤ e^{-θt} ∫ tr e^{θY} dμ`. -/
theorem measureReal_le_lambdaMax_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → Matrix n n 𝕜} (hY : ∀ ω, (Y ω).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (traceMgf Y θ) μ) (t : ℝ) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤ Real.exp (-θ * t) * ∫ ω, traceMgf Y θ ω ∂μ := by
  have hsub : {ω | t ≤ (hY ω).lambdaMax} ⊆ {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω} := by
    intro ω hω
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ.le)).trans
      ((hY ω).exp_mul_lambdaMax_le_re_trace_exp θ)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (hY ω).re_trace_exp_nonneg θ) hint (Real.exp (θ * t))
  have hmono := measureReal_mono hsub (μ := μ)
  calc μ.real {ω | t ≤ (hY ω).lambdaMax}
      ≤ μ.real {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω} := hmono
    _ = Real.exp (-θ * t) * (Real.exp (θ * t) *
          μ.real {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω}) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-θ * t) * ∫ ω, traceMgf Y θ ω ∂μ :=
        mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le

/-- **Matrix Laplace transform method, lower tail** (Tropp, arXiv:1501.01571,
Proposition 3.2.1, display (3.2.2)). Let `Y` be a random Hermitian matrix on a finite measure
space, and let `θ < 0` be such that `ω ↦ tr e^{θY(ω)}` is integrable. Then for every real `t`,
`μ{λmin(Y) ≤ t} ≤ e^{-θt} ∫ tr e^{θY} dμ`. -/
theorem measureReal_lambdaMin_le_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → Matrix n n 𝕜} (hY : ∀ ω, (Y ω).IsHermitian) {θ : ℝ} (hθ : θ < 0)
    (hint : Integrable (traceMgf Y θ) μ) (t : ℝ) :
    μ.real {ω | (hY ω).lambdaMin ≤ t} ≤ Real.exp (-θ * t) * ∫ ω, traceMgf Y θ ω ∂μ := by
  have hsub : {ω | (hY ω).lambdaMin ≤ t} ⊆ {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω} := by
    intro ω hω
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hω hθ.le)).trans
      ((hY ω).exp_mul_lambdaMin_le_re_trace_exp θ)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (hY ω).re_trace_exp_nonneg θ) hint (Real.exp (θ * t))
  have hmono := measureReal_mono hsub (μ := μ)
  calc μ.real {ω | (hY ω).lambdaMin ≤ t}
      ≤ μ.real {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω} := hmono
    _ = Real.exp (-θ * t) * (Real.exp (θ * t) *
          μ.real {ω | Real.exp (θ * t) ≤ traceMgf Y θ ω}) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-θ * t) * ∫ ω, traceMgf Y θ ω ∂μ :=
        mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le

/-- **Matrix Laplace transform method, expectation bound** (Tropp, arXiv:1501.01571,
Proposition 3.2.2, display (3.2.4)). Let `Y` be a random Hermitian matrix on a probability
space such that `λmax(Y)` is integrable, and let `θ > 0` be such that `ω ↦ tr e^{θY(ω)}` is
integrable. Then `E λmax(Y) ≤ θ⁻¹ log E tr e^{θY}`. -/
theorem integral_lambdaMax_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → Matrix n n 𝕜} (hY : ∀ ω, (Y ω).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (hmax : Integrable (fun ω => (hY ω).lambdaMax) μ)
    (hint : Integrable (traceMgf Y θ) μ) :
    ∫ ω, (hY ω).lambdaMax ∂μ ≤ θ⁻¹ * Real.log (∫ ω, traceMgf Y θ ω ∂μ) := by
  set L : Ω → ℝ := fun ω => (hY ω).lambdaMax with hL
  have hpt : ∀ ω, Real.exp (θ * L ω) ≤ traceMgf Y θ ω := fun ω =>
    (hY ω).exp_mul_lambdaMax_le_re_trace_exp θ
  have hexp_meas : AEStronglyMeasurable (fun ω => Real.exp (θ * L ω)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
      hmax.aestronglyMeasurable
  have hexp_int : Integrable (fun ω => Real.exp (θ * L ω)) μ :=
    hint.mono' hexp_meas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω)
  have hθL : Integrable (fun ω => θ * L ω) μ := hmax.const_mul θ
  -- Jensen: `exp (E[θ L]) ≤ E[exp (θ L)]`.
  have hjensen : Real.exp (∫ ω, θ * L ω ∂μ) ≤ ∫ ω, Real.exp (θ * L ω) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hθL hexp_int
  have hle : ∫ ω, Real.exp (θ * L ω) ∂μ ≤ ∫ ω, traceMgf Y θ ω ∂μ :=
    integral_mono hexp_int hint hpt
  have hlog : θ * ∫ ω, L ω ∂μ ≤ Real.log (∫ ω, traceMgf Y θ ω ∂μ) := by
    rw [← integral_const_mul, ← Real.log_exp (∫ ω, θ * L ω ∂μ)]
    exact Real.log_le_log (Real.exp_pos _) (hjensen.trans hle)
  rw [le_inv_mul_iff₀ hθ]
  exact hlog

end MathlibExt.Probability.MatrixLaplaceTransform
