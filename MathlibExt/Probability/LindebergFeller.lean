/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Lindeberg–Feller central limit theorem

For a triangular array `X n k` of independent, mean-zero random variables,
if the row variances `∑ₖ E[(X n k)²]` converge to `σ² > 0` and the
Lindeberg condition holds (the truncated second moments
`∑ₖ E[(X n k)² · 𝟙{|X n k| > ε}]` tend to `0` for every `ε > 0`), then
the row sums `Sₙ = ∑ₖ X n k` converge in distribution to `N(0, σ²)`.

## Source

This formalizes the target "Theorem (Lindeberg-Feller theorem)" of
`v1/Atlas/TheoryOfProbability/targets.yaml`, whose v1 formalization is
`v1/Atlas/TheoryOfProbability/code/LindebergFeller.lean`.

## Correction to the v1 statement (please read)

The v1 statement is **false as formalized**: its hypotheses do not force
the summands to be square-integrable, and in Lean the Bochner integral
of a non-integrable function is `0` by convention, so the variance sums
and the Lindeberg sums can hold vacuously while the conclusion fails.
Counterexample: put the same Cauchy variable `C` in position `k = 0` of
every row (and suitable Gaussians in the other positions so the row
variance sums are exactly `σ²`). Then every `∫ (X n k)² ∂μ` is either
the genuine Gaussian second moment or `0` by the non-integrability
convention, the Lindeberg sums are `0` for the Cauchy term for the same
reason, and `∫ X n k ∂μ = 0` holds vacuously for the Cauchy term — so
all of v1's hypotheses hold — but the characteristic-function product
acquires an extra factor `E[e^{itC}] = e^{-|t|}`, and the row sums
converge in distribution to `N(0, σ²)` convolved with a Cauchy law,
not to `N(0, σ²)`.

This file therefore adds the hypothesis the book's statement takes for
granted:

  `hint2 : ∀ n, ∀ k ∈ Finset.range n, Integrable (fun ω => (X n k ω) ^ 2) μ`.

With it, every variance and Lindeberg integral is a genuine expectation
and the classical characteristic-function proof goes through.

## Proof outline

The main theorem follows from the characteristic-function convergence
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) plus the analytic
core `lindeberg_charFun_product_tendsto`: the product of the row
characteristic functions tends to `exp(-σ²t²/2)`. The core is proved
by expanding each characteristic function to second order,
`φ_{nk}(t) - 1 + (t²/2) E[X_{nk}²] = ∫ (e^{itX} - 1 - itX + t²X²/2)`,
splitting the integral at a truncation level `ε` (the small part is
controlled by the third-order Taylor bound for `exp`, the large part
by the Lindeberg condition), and comparing the product with
`exp` of the sum of the first-order terms via the comparison lemma
`prod_one_add_sub_exp_sum_le`.

## Main results

* `ProbabilityTheory.LindebergConditionTriangular`: the Lindeberg
  condition for a triangular array.
* `ProbabilityTheory.lindeberg_charFun_product_tendsto`: under the
  Lindeberg hypothesis, the product of the row characteristic functions
  converges to the Gaussian characteristic function.
* `ProbabilityTheory.lindeberg_feller_clt_triangular`: the
  Lindeberg–Feller central limit theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal ENNReal

namespace ProbabilityTheory

/-- The **Lindeberg condition** for a triangular array `X n k` of random variables
on `(Ω, μ)`: for every `ε > 0`, the truncated second moment
`∑ₖ ∫ (X n k)² · 𝟙{|X n k| > ε} dμ` tends to `0` as `n → ∞`. This is the key
hypothesis of the Lindeberg–Feller central limit theorem. -/
def LindebergConditionTriangular {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)
    atTop (𝓝 0)

/-- Second-order Taylor estimate for the complex exponential along the
imaginary axis, in the range where it is needed: if `‖x‖ ≤ 1` then
`‖e^{ix} - 1 - ix‖ ≤ x²`. -/
theorem norm_exp_ofReal_mul_I_sub_one_sub_le {x : ℝ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.exp (↑x * Complex.I) - 1 - ↑x * Complex.I‖ ≤ x ^ 2 := by
  have h : ‖(↑x * Complex.I : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    exact hx
  have h2 := Complex.norm_exp_sub_one_sub_id_le h
  rwa [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    sq_abs] at h2

/-- Comparison between a finite product `∏ (1 + uᵢ)` and the exponential
of the sum `∑ uᵢ`: if every `‖uᵢ‖ ≤ 1 / 2`, then
`‖∏ (1 + uᵢ) - exp(∑ uᵢ)‖ ≤ (∑ ‖uᵢ‖²) · exp(∑ ‖uᵢ‖)`.
This is the estimate that turns the second-order expansion of each
characteristic function into convergence of the product. -/
theorem prod_one_add_sub_exp_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1 / 2) :
    ‖∏ i ∈ s, (1 + u i) - Complex.exp (∑ i ∈ s, u i)‖ ≤
      (∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (∑ i ∈ s, ‖u i‖) := by
  revert hu
  refine Finset.induction ?_ ?_ s
  · intro _
    simp
  · intro a s ha ih hu
    have hu_s : ∀ i ∈ s, ‖u i‖ ≤ 1 / 2 :=
      fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hua : ‖u a‖ ≤ 1 / 2 := hu a (Finset.mem_insert_self a s)
    have ih' := ih hu_s
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      Finset.prod_insert ha, Complex.exp_add]
    have hE : ‖Complex.exp (∑ i ∈ s, u i)‖ ≤ Real.exp (∑ i ∈ s, ‖u i‖) := by
      calc ‖Complex.exp (∑ i ∈ s, u i)‖ ≤ Real.exp ‖∑ i ∈ s, u i‖ :=
            Complex.norm_exp_le_exp_norm _
        _ ≤ Real.exp (∑ i ∈ s, ‖u i‖) :=
            Real.exp_le_exp.mpr (norm_sum_le _ _)
    have hdiff : (1 + u a) * ∏ i ∈ s, (1 + u i) -
        Complex.exp (u a) * Complex.exp (∑ i ∈ s, u i)
        = (1 + u a) * (∏ i ∈ s, (1 + u i) - Complex.exp (∑ i ∈ s, u i)) +
          ((1 + u a) - Complex.exp (u a)) * Complex.exp (∑ i ∈ s, u i) := by
      ring
    have hquad : ‖(1 + u a) - Complex.exp (u a)‖ ≤ ‖u a‖ ^ 2 := by
      have h1 := Complex.norm_exp_sub_one_sub_id_le (by linarith : ‖u a‖ ≤ 1)
      have : ‖Complex.exp (u a) - 1 - u a‖ = ‖(1 + u a) - Complex.exp (u a)‖ := by
        rw [← norm_neg]
        congr 1
        ring
      rwa [this] at h1
    calc ‖(1 + u a) * ∏ i ∈ s, (1 + u i) -
            Complex.exp (u a) * Complex.exp (∑ i ∈ s, u i)‖
        = ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - Complex.exp (∑ i ∈ s, u i)) +
          ((1 + u a) - Complex.exp (u a)) * Complex.exp (∑ i ∈ s, u i)‖ := by
          rw [hdiff]
      _ ≤ ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - Complex.exp (∑ i ∈ s, u i))‖ +
          ‖((1 + u a) - Complex.exp (u a)) * Complex.exp (∑ i ∈ s, u i)‖ :=
          norm_add_le _ _
      _ ≤ (1 + ‖u a‖) * ((∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (∑ i ∈ s, ‖u i‖)) +
          ‖u a‖ ^ 2 * Real.exp (∑ i ∈ s, ‖u i‖) := by
          apply add_le_add
          · rw [norm_mul]
            exact mul_le_mul (by simpa using norm_add_le (1 : ℂ) (u a)) ih'
              (norm_nonneg _) (by positivity)
          · rw [norm_mul]
            exact mul_le_mul hquad hE (norm_nonneg _) (by positivity)
      _ ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) +
          ‖u a‖ ^ 2 * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) := by
          have h1 : (1 + ‖u a‖) * ((∑ i ∈ s, ‖u i‖ ^ 2) *
              Real.exp (∑ i ∈ s, ‖u i‖)) ≤
              (∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) := by
            have hexp : (1 + ‖u a‖) * Real.exp (∑ i ∈ s, ‖u i‖) ≤
                Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) := by
              calc (1 + ‖u a‖) * Real.exp (∑ i ∈ s, ‖u i‖)
                  ≤ Real.exp ‖u a‖ * Real.exp (∑ i ∈ s, ‖u i‖) :=
                    mul_le_mul_of_nonneg_right
                        (by simpa [add_comm] using Real.add_one_le_exp (‖u a‖))
                        (Real.exp_nonneg _)
                _ = Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) := (Real.exp_add _ _).symm
            calc (1 + ‖u a‖) * ((∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (∑ i ∈ s, ‖u i‖))
                = (∑ i ∈ s, ‖u i‖ ^ 2) * ((1 + ‖u a‖) * Real.exp (∑ i ∈ s, ‖u i‖)) := by
                  ring
              _ ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) :=
                  mul_le_mul_of_nonneg_left hexp (Finset.sum_nonneg fun i _ => sq_nonneg _)
          have h2 : ‖u a‖ ^ 2 * Real.exp (∑ i ∈ s, ‖u i‖) ≤
              ‖u a‖ ^ 2 * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (le_add_of_nonneg_left (norm_nonneg _))) (sq_nonneg _)
          exact add_le_add h1 h2
      _ = (‖u a‖ ^ 2 + ∑ i ∈ s, ‖u i‖ ^ 2) * Real.exp (‖u a‖ + ∑ i ∈ s, ‖u i‖) := by
          ring

/-- The second-order Taylor remainder of `e^{itx}`:
`e^{itx} - 1 - itx + (tx)²/2`, written so that it equals
`exp z - (1 + z + z²/2)` for `z = itx`. -/
private noncomputable def lindebergExpansionTerm (t x : ℝ) : ℂ :=
  Complex.exp (↑t * ↑x * Complex.I) - 1 - ↑t * ↑x * Complex.I +
    (↑t * ↑x) ^ 2 / 2

/-- The expansion term is the third-order remainder of the exponential
Taylor series: `e^z - (1 + z + z²/2)` with `z = itx`. -/
private lemma lindebergExpansionTerm_eq (t x : ℝ) :
    lindebergExpansionTerm t x = Complex.exp (↑t * ↑x * Complex.I) -
      ∑ m ∈ Finset.range 3, (↑t * ↑x * Complex.I) ^ m / (m.factorial : ℂ) := by
  have hz2 : (↑t * ↑x * Complex.I) ^ 2 = -(↑t * ↑x) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  simp only [lindebergExpansionTerm, Finset.sum_range_succ, Finset.sum_range_zero,
    hz2, Nat.factorial]
  ring

/-- **Analytic core of the Lindeberg–Feller theorem.** Under the Lindeberg
hypothesis (plus genuine square-integrability of the summands), the
product of the row characteristic functions converges to the Gaussian
characteristic function `exp(-σ²t²/2)`. -/
theorem lindeberg_charFun_product_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n, ∀ k ∈ Finset.range n, Measurable (X n k))
    (hmean : ∀ n, ∀ k ∈ Finset.range n, ∫ ω, X n k ω ∂μ = 0)
    (hint2 : ∀ n, ∀ k ∈ Finset.range n, Integrable (fun ω => (X n k ω) ^ 2) μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : Tendsto (fun n => ∑ k ∈ Finset.range n,
              ∫ ω, (X n k ω) ^ 2 ∂μ) atTop (𝓝 (σ ^ 2)))
    (hL : LindebergConditionTriangular X μ)
    (t : ℝ) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t)
      atTop (𝓝 (Complex.exp (-(↑(σ ^ 2) * ↑t ^ 2 / 2)))) := by
  by_cases ht : t = 0
  · subst ht
    have h1 : ∀ n, ∀ k ∈ Finset.range n, charFun (μ.map (X n k)) (0 : ℝ) = 1 := by
      intro n k hk
      have : IsProbabilityMeasure (μ.map (X n k)) :=
        (MeasureTheory.Measure.isProbabilityMeasure_map_iff
          (hmeas n k hk).aemeasurable).mpr inferInstance
      simp [charFun_zero]
    have hprod1 : (fun n => ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) (0 : ℝ)) =
        fun _ => 1 := by
      funext n
      exact Finset.prod_eq_one (fun k hk => h1 n k hk)
    rw [hprod1]
    simp
  -- Integrability of the summands follows from square-integrability.
  have hX_int : ∀ n, ∀ k ∈ Finset.range n, Integrable (X n k) μ := by
    intro n k hk
    have hmem : MemLp (X n k) 2 μ :=
      (memLp_two_iff_integrable_sq (hmeas n k hk).aestronglyMeasurable).mpr (hint2 n k hk)
    exact hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hE2_nonneg : ∀ n k, 0 ≤ ∫ ω, (X n k ω) ^ 2 ∂μ :=
    fun n k => integral_nonneg fun ω => sq_nonneg _
  -- Characteristic function as an integral over `Ω`.
  have hchar : ∀ n, ∀ k ∈ Finset.range n, charFun (μ.map (X n k)) t
      = ∫ ω, Complex.exp (↑t * ↑(X n k ω) * Complex.I) ∂μ := by
    intro n k hk
    rw [charFun_apply_real, integral_map (hmeas n k hk).aemeasurable (by fun_prop)]
  -- Integrability of the pieces of the expansion term.
  have hexp : ∀ n, ∀ k ∈ Finset.range n, Integrable
      (fun ω => Complex.exp (↑t * ↑(X n k ω) * Complex.I)) μ := by
    intro n k hk
    have hm : Measurable (X n k) := hmeas n k hk
    apply (integrable_const (1 : ℝ)).mono'
    · exact (by fun_prop : AEStronglyMeasurable
        (fun ω => Complex.exp (↑t * ↑(X n k ω) * Complex.I)) μ)
    · exact Filter.Eventually.of_forall fun ω => by
        rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hlin : ∀ n, ∀ k ∈ Finset.range n,
      Integrable (fun ω => ↑t * Complex.I * (↑(X n k ω) : ℂ)) μ := by
    intro n k hk
    exact ((hX_int n k hk).ofReal).const_mul (↑t * Complex.I)
  have hsq : ∀ n, ∀ k ∈ Finset.range n, Integrable
      (fun ω => (↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ)) μ := by
    intro n k hk
    exact ((hint2 n k hk).ofReal).const_mul (↑(t ^ 2 / 2 : ℝ) : ℂ)
  -- Pointwise form of the expansion term.
  have hterm : ∀ n k ω, lindebergExpansionTerm t (X n k ω) =
      Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
        (↑t * Complex.I * (↑(X n k ω) : ℂ)) +
        ((↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ)) := by
    intro n k ω
    simp only [lindebergExpansionTerm]
    push_cast
    ring
  -- The expansion term is integrable.
  have hF_int : ∀ n, ∀ k ∈ Finset.range n,
      Integrable (fun ω => lindebergExpansionTerm t (X n k ω)) μ := by
    intro n k hk
    have hparts : Integrable (fun ω => Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
        (↑t * Complex.I * (↑(X n k ω) : ℂ)) +
        ((↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ))) μ :=
      (((hexp n k hk).sub (integrable_const (1 : ℂ))).sub (hlin n k hk)).add (hsq n k hk)
    exact hparts.congr (Filter.Eventually.of_forall fun ω => (hterm n k ω).symm)
  -- Integral representation of the second-order expansion error.
  have hRep : ∀ n, ∀ k ∈ Finset.range n, charFun (μ.map (X n k)) t - 1 +
        (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)
      = ∫ ω, lindebergExpansionTerm t (X n k ω) ∂μ := by
    intro n k hk
    have hsplit : ∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
        (↑t * Complex.I * (↑(X n k ω) : ℂ)) +
        ((↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ))) ∂μ =
        ((∫ ω, Complex.exp (↑t * ↑(X n k ω) * Complex.I) ∂μ - ∫ _ : Ω, (1 : ℂ) ∂μ) -
          ∫ ω, ↑t * Complex.I * (↑(X n k ω) : ℂ) ∂μ) +
        ∫ ω, (↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ) ∂μ := by
      rw [show (∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
            (↑t * Complex.I * (↑(X n k ω) : ℂ)) +
            ((↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ))) ∂μ =
          ∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
            (↑t * Complex.I * (↑(X n k ω) : ℂ))) ∂μ +
          ∫ ω, (↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ) ∂μ) from
        integral_add (by exact (Integrable.sub (Integrable.sub (hexp n k hk)
          (integrable_const (1 : ℂ))) (hlin n k hk))) (hsq n k hk),
        show (∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
            (↑t * Complex.I * (↑(X n k ω) : ℂ))) ∂μ =
          ∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ -
          ∫ ω, ↑t * Complex.I * (↑(X n k ω) : ℂ) ∂μ) from
        integral_sub (by exact (Integrable.sub (hexp n k hk) (integrable_const (1 : ℂ))))
          (hlin n k hk),
        show (∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ =
          ∫ ω, Complex.exp (↑t * ↑(X n k ω) * Complex.I) ∂μ - ∫ _ : Ω, (1 : ℂ) ∂μ) from
        integral_sub (hexp n k hk) (integrable_const (1 : ℂ))]
    rw [integral_congr_ae (Filter.Eventually.of_forall (hterm n k)), hsplit]
    rw [← hchar n k hk]
    have h1 : ∫ _ : Ω, (1 : ℂ) ∂μ = 1 := by simp
    have h2 : ∫ ω, ↑t * Complex.I * (↑(X n k ω) : ℂ) ∂μ = 0 := by
      rw [integral_const_mul, integral_complex_ofReal, hmean n k hk]
      simp
    have h3 : ∫ ω, (↑(t ^ 2 / 2 : ℝ) : ℂ) * (↑((X n k ω) ^ 2) : ℂ) ∂μ
        = (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_complex_ofReal]
    rw [h1, h2, h3]
    simp
  -- Truncation bound for the expansion error.
  have hC : ∀ (ε : ℝ), 0 < ε → |t| * ε ≤ 1 → ∀ n, ∀ k ∈ Finset.range n,
      ‖charFun (μ.map (X n k)) t - 1 +
        (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ ≤
        |t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) +
          (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) *
            ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ := by
    intro ε hε hεt n k hk
    rw [hRep n k hk]
    set A : Set Ω := {ω | ε < |X n k ω|} with hA
    have hAmeas : MeasurableSet A := by
      have h := measurableSet_lt (f := fun _ : Ω => ε) (g := fun ω => ‖X n k ω‖)
        measurable_const (hmeas n k hk).norm
      rw [hA]
      simpa [Real.norm_eq_abs] using h
    rw [← integral_add_compl hAmeas (hF_int n k hk)]
    -- Small part: `|X| ≤ ε`, third-order Taylor bound.
    have hsmall : ‖∫ ω in Aᶜ, lindebergExpansionTerm t (X n k ω) ∂μ‖ ≤
        |t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) := by
      have hpoint : ∀ ω ∈ Aᶜ, ‖lindebergExpansionTerm t (X n k ω)‖ ≤
          |t| ^ 3 * ε * Real.exp 1 * (X n k ω) ^ 2 := by
        intro ω hω
        have hXω : |X n k ω| ≤ ε := by
          simp only [Set.mem_compl_iff, hA, Set.mem_ofPred_eq, not_lt] at hω
          exact hω
        have hz : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ ≤ 1 := by
          have hzn : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ = |t| * |X n k ω| := by
            rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
              Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
          rw [hzn]
          calc |t| * |X n k ω| ≤ |t| * ε :=
                mul_le_mul_of_nonneg_left hXω (abs_nonneg _)
            _ ≤ 1 := hεt
        have h3 := Complex.norm_exp_sub_sum_le_norm_mul_exp
          (↑t * ↑(X n k ω) * Complex.I) 3
        rw [← lindebergExpansionTerm_eq] at h3
        have hX3 : |X n k ω| ^ 3 ≤ ε * (X n k ω) ^ 2 := by
          calc |X n k ω| ^ 3 = |X n k ω| ^ 2 * |X n k ω| := by rw [pow_succ]
            _ = (X n k ω) ^ 2 * |X n k ω| := by rw [sq_abs]
            _ ≤ (X n k ω) ^ 2 * ε :=
                mul_le_mul_of_nonneg_left hXω (sq_nonneg _)
            _ = ε * (X n k ω) ^ 2 := by ring
        calc ‖lindebergExpansionTerm t (X n k ω)‖ ≤
                ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ ^ 3 *
                  Real.exp ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ := h3
          _ ≤ (|t| * |X n k ω|) ^ 3 * Real.exp 1 := by
              have hzn : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ = |t| * |X n k ω| := by
                rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
                  Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
                  Real.norm_eq_abs]
              have hzn_le : |t| * |X n k ω| ≤ 1 := hzn ▸ hz
              rw [hzn]
              exact mul_le_mul (le_refl _) (Real.exp_le_exp.mpr hzn_le) (Real.exp_nonneg _)
                (by positivity)
          _ = |t| ^ 3 * |X n k ω| ^ 3 * Real.exp 1 := by rw [mul_pow]
          _ ≤ |t| ^ 3 * (ε * (X n k ω) ^ 2) * Real.exp 1 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hX3 (by positivity)) (Real.exp_nonneg _)
          _ = |t| ^ 3 * ε * Real.exp 1 * (X n k ω) ^ 2 := by ring
      calc ‖∫ ω in Aᶜ, lindebergExpansionTerm t (X n k ω) ∂μ‖
          ≤ ∫ ω in Aᶜ, |t| ^ 3 * ε * Real.exp 1 * (X n k ω) ^ 2 ∂μ :=
            norm_integral_le_of_norm_le
              ((hint2 n k hk).const_mul _).integrableOn
              (ae_restrict_of_forall_mem hAmeas.compl hpoint)
        _ ≤ ∫ ω, |t| ^ 3 * ε * Real.exp 1 * (X n k ω) ^ 2 ∂μ :=
            setIntegral_le_integral ((hint2 n k hk).const_mul _)
              (Filter.Eventually.of_forall fun ω => by positivity)
        _ = |t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) := by
            rw [integral_const_mul]
    -- Large part: `|X| > ε`, crude bound plus the Lindeberg term.
    have hlarge : ‖∫ ω in A, lindebergExpansionTerm t (X n k ω) ∂μ‖ ≤
        (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) *
          ∫ ω, (X n k ω) ^ 2 * Set.indicator A 1 ω ∂μ := by
      have hpoint : ∀ ω ∈ A, ‖lindebergExpansionTerm t (X n k ω)‖ ≤
          2 + |t| * |X n k ω| + (t ^ 2 / 2) * (X n k ω) ^ 2 := by
        intro ω hω
        have hexp1 : ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ = 1 := by
          rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
        have hlin1 : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ = |t| * |X n k ω| := by
          rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
            Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
        have hsq1 : ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ = (t ^ 2 / 2) * (X n k ω) ^ 2 := by
          rw [norm_div, norm_pow]
          have hnn : ‖(↑t * ↑(X n k ω) : ℂ)‖ = |t| * |X n k ω| := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
          rw [hnn, mul_pow, sq_abs, sq_abs]
          have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [h2n]
          ring
        have h4 : ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
            ↑t * ↑(X n k ω) * Complex.I + (↑t * ↑(X n k ω)) ^ 2 / 2‖ ≤
            ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + 1 +
              ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ +
                ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ := by
          calc ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                  ↑t * ↑(X n k ω) * Complex.I + (↑t * ↑(X n k ω)) ^ 2 / 2‖
              = ‖(Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                  ↑t * ↑(X n k ω) * Complex.I) + (↑t * ↑(X n k ω)) ^ 2 / 2‖ := by
                ring_nf
            _ ≤ ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                  ↑t * ↑(X n k ω) * Complex.I‖ +
                    ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ := norm_add_le _ _
            _ ≤ (‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + ‖(1 : ℂ)‖ +
                  ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖) +
                    ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ := by
                have hinner : ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                        ↑t * ↑(X n k ω) * Complex.I‖ ≤
                    (‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + ‖(1 : ℂ)‖) +
                      ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ := by
                  calc ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                          ↑t * ↑(X n k ω) * Complex.I‖
                      ≤ ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1‖ +
                          ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ := norm_sub_le _ _
                    _ ≤ (‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + ‖(1 : ℂ)‖) +
                          ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ :=
                        add_le_add (norm_sub_le _ _) (le_refl _)
                exact add_le_add hinner (le_refl _)
            _ = ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + 1 +
                  ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ +
                    ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ := by
                rw [norm_one]
        show ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
              ↑t * ↑(X n k ω) * Complex.I + (↑t * ↑(X n k ω)) ^ 2 / 2‖ ≤ _
        calc ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1 -
                ↑t * ↑(X n k ω) * Complex.I + (↑t * ↑(X n k ω)) ^ 2 / 2‖
            ≤ ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + 1 +
                ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ +
                  ‖((↑t * ↑(X n k ω) : ℂ)) ^ 2 / 2‖ := h4
          _ = 2 + |t| * |X n k ω| + (t ^ 2 / 2) * (X n k ω) ^ 2 := by
              rw [hexp1, hlin1, hsq1]
              ring
      have hbound_int : IntegrableOn
          (fun ω => 2 + |t| * |X n k ω| + (t ^ 2 / 2) * (X n k ω) ^ 2) A μ := by
        apply IntegrableOn.add
        · apply IntegrableOn.add
          · exact integrableOn_const
          · exact ((hX_int n k hk).abs.const_mul |t|).integrableOn
        · exact ((hint2 n k hk).const_mul (t ^ 2 / 2)).integrableOn
      have hCpoint : ∀ ω ∈ A, 2 + |t| * |X n k ω| + (t ^ 2 / 2) * (X n k ω) ^ 2 ≤
          (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) * (X n k ω) ^ 2 := by
        intro ω hω
        have hω' : ε < |X n k ω| := hω
        have hε2 : ε ^ 2 ≤ (X n k ω) ^ 2 := by
          have h := sq_le_sq' (a := ε) (b := |X n k ω|)
            (by linarith [abs_nonneg (X n k ω)]) (le_of_lt hω')
          rwa [sq_abs] at h
        have h1 : (2 : ℝ) ≤ (2 / ε ^ 2) * (X n k ω) ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
          nlinarith [hε2]
        have h2 : |t| * |X n k ω| ≤ (|t| / ε) * (X n k ω) ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]
          nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hω')
            (mul_nonneg (abs_nonneg t) (abs_nonneg (X n k ω))), sq_abs (X n k ω)]
        nlinarith [h1, h2]
      calc ‖∫ ω in A, lindebergExpansionTerm t (X n k ω) ∂μ‖
          ≤ ∫ ω in A, (2 + |t| * |X n k ω| + (t ^ 2 / 2) * (X n k ω) ^ 2) ∂μ :=
            norm_integral_le_of_norm_le hbound_int
              (ae_restrict_of_forall_mem hAmeas hpoint)
        _ ≤ ∫ ω in A, (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) * (X n k ω) ^ 2 ∂μ :=
            setIntegral_mono_on hbound_int
              ((hint2 n k hk).const_mul _).integrableOn hAmeas hCpoint
        _ = (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) * ∫ ω in A, (X n k ω) ^ 2 ∂μ := by
            rw [integral_const_mul]
        _ = (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) *
              ∫ ω, (X n k ω) ^ 2 * Set.indicator A 1 ω ∂μ := by
            congr 1
            have hInd : (fun ω => (X n k ω) ^ 2 * Set.indicator A 1 ω) =
                Set.indicator A (fun ω => (X n k ω) ^ 2) := by
              funext ω
              by_cases hω : ω ∈ A <;> simp [hω]
            rw [hInd, integral_indicator hAmeas]
    calc ‖∫ ω in A, lindebergExpansionTerm t (X n k ω) ∂μ +
            ∫ ω in Aᶜ, lindebergExpansionTerm t (X n k ω) ∂μ‖
        ≤ ‖∫ ω in A, lindebergExpansionTerm t (X n k ω) ∂μ‖ +
            ‖∫ ω in Aᶜ, lindebergExpansionTerm t (X n k ω) ∂μ‖ := norm_add_le _ _
      _ ≤ (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) *
            ∫ ω, (X n k ω) ^ 2 * Set.indicator A 1 ω ∂μ +
            |t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) :=
          add_le_add hlarge hsmall
      _ = |t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) +
            (2 / ε ^ 2 + |t| / ε + t ^ 2 / 2) *
              ∫ ω, (X n k ω) ^ 2 * Set.indicator A 1 ω ∂μ := by ring
  -- The Lindeberg term equals the set integral over `{|X| > ε}`.
  have hLterm_eq : ∀ n, ∀ k ∈ Finset.range n, ∀ (ε : ℝ), 0 < ε →
      ∫ ω in {ω | ε < |X n k ω|}, (X n k ω) ^ 2 ∂μ =
        ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ := by
    intro n k hk ε hε
    have hAmeas : MeasurableSet {ω | ε < |X n k ω|} := by
      have h := measurableSet_lt (f := fun _ : Ω => ε) (g := fun ω => ‖X n k ω‖)
        measurable_const (hmeas n k hk).norm
      simpa [Real.norm_eq_abs] using h
    have hInd : (fun ω => (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω) =
        Set.indicator {ω | ε < |X n k ω|} (fun ω => (X n k ω) ^ 2) := by
      funext ω
      by_cases hω : ω ∈ {ω | ε < |X n k ω|} <;> simp [hω]
    rw [hInd, integral_indicator hAmeas]
  -- The Lindeberg terms are nonnegative.
  have hLterm_nonneg : ∀ n k (ε : ℝ),
      0 ≤ ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ := by
    intro n k ε
    exact integral_nonneg fun ω => mul_nonneg (sq_nonneg _)
      (by by_cases hω : ε < |X n k ω| <;> simp [hω])
  -- Uniform smallness of the second moments, from the Lindeberg condition.
  have hE2_unif : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ k ∈ Finset.range n,
      ∫ ω, (X n k ω) ^ 2 ∂μ < η := by
    intro η hη
    set ε₁ := Real.sqrt (η / 2) with hε₁
    have hε₁pos : 0 < ε₁ := Real.sqrt_pos.mpr (by positivity)
    have hε₁sq : ε₁ ^ 2 = η / 2 := by
      rw [hε₁, Real.sq_sqrt (by positivity)]
    have hev : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n,
        ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε₁ < |X n k ω'|} 1 ω ∂μ) < η / 2 := by
      have h := (hL ε₁ hε₁pos).eventually
        (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < η / 2))
      filter_upwards [h] with n hn
      rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k _ => hLterm_nonneg n k ε₁)] at hn
      exact hn
    filter_upwards [hev] with n hn k hk
    have hAmeas : MeasurableSet {ω | ε₁ < |X n k ω|} := by
      have h := measurableSet_lt (f := fun _ : Ω => ε₁) (g := fun ω => ‖X n k ω‖)
        measurable_const (hmeas n k hk).norm
      simpa [Real.norm_eq_abs] using h
    have hsplit : ∫ ω, (X n k ω) ^ 2 ∂μ =
        ∫ ω in {ω | ε₁ < |X n k ω|}, (X n k ω) ^ 2 ∂μ +
        ∫ ω in {ω | ε₁ < |X n k ω|}ᶜ, (X n k ω) ^ 2 ∂μ :=
      (integral_add_compl hAmeas (hint2 n k hk)).symm
    have hsmall : ∫ ω in {ω | ε₁ < |X n k ω|}ᶜ, (X n k ω) ^ 2 ∂μ ≤ η / 2 := by
      calc ∫ ω in {ω | ε₁ < |X n k ω|}ᶜ, (X n k ω) ^ 2 ∂μ
          ≤ ∫ ω in {ω | ε₁ < |X n k ω|}ᶜ, ε₁ ^ 2 ∂μ :=
            setIntegral_mono_on (hint2 n k hk).integrableOn (integrableOn_const)
              hAmeas.compl (fun ω hω => by
                simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
                rw [← sq_abs]
                exact sq_le_sq' (by linarith [abs_nonneg (X n k ω), hε₁pos.le]) hω)
        _ = ε₁ ^ 2 * μ.real {ω | ε₁ < |X n k ω|}ᶜ := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ (η / 2) * 1 := by
            rw [← hε₁sq]
            exact mul_le_mul_of_nonneg_left
              (by
                have h2 : μ {ω | ε₁ < |X n k ω|}ᶜ ≤ 1 :=
                  (measure_mono (Set.subset_univ _)).trans_eq measure_univ
                calc μ.real {ω | ε₁ < |X n k ω|}ᶜ = (μ {ω | ε₁ < |X n k ω|}ᶜ).toReal := rfl
                  _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h2
                  _ = 1 := ENNReal.toReal_one)
              (by positivity)
        _ = η / 2 := by ring
    have hterm_le : ∫ ω in {ω | ε₁ < |X n k ω|}, (X n k ω) ^ 2 ∂μ < η / 2 := by
      calc ∫ ω in {ω | ε₁ < |X n k ω|}, (X n k ω) ^ 2 ∂μ
          = ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε₁ < |X n k ω'|} 1 ω ∂μ :=
            hLterm_eq n k hk ε₁ hε₁pos
        _ ≤ ∑ j ∈ Finset.range n,
              ∫ ω, (X n j ω) ^ 2 * Set.indicator {ω' | ε₁ < |X n j ω'|} 1 ω ∂μ :=
            Finset.single_le_sum (fun j _ => hLterm_nonneg n j ε₁) hk
        _ < η / 2 := hn
    linarith [hsplit, hsmall, hterm_le]
  -- The expansion errors are summable to `0`.
  have hSumE : Tendsto (fun n => ∑ k ∈ Finset.range n,
      ‖charFun (μ.map (X n k)) t - 1 +
        (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖) atTop (𝓝 0) := by
    have hfrac : ∀ {C η : ℝ}, 0 ≤ C → 0 < η → C * (η / (2 * (C + 1))) < η / 2 := by
      intro C η hC hη
      rw [mul_div_assoc', div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))]
      nlinarith [hC, hη, mul_nonneg hC hη.le]
    rw [Metric.tendsto_atTop]
    intro η hη
    set B := |t| ^ 3 * Real.exp 1 * (σ ^ 2 + 1) with hB
    have hBnn : 0 ≤ B := by positivity
    set ε := min (1 / |t|) (η / (2 * (B + 1))) with hεdef
    have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
    have hεt : |t| * ε ≤ 1 := by
      have hle : ε ≤ 1 / |t| := min_le_left _ _
      calc |t| * ε ≤ |t| * (1 / |t|) :=
            mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = 1 := mul_one_div_cancel (ne_of_gt (abs_pos.mpr ht))
    have hA1 : |t| ^ 3 * ε * Real.exp 1 * (σ ^ 2 + 1) < η / 2 := by
      have hεle : ε ≤ η / (2 * (B + 1)) := min_le_right _ _
      calc |t| ^ 3 * ε * Real.exp 1 * (σ ^ 2 + 1)
          ≤ |t| ^ 3 * (η / (2 * (B + 1))) * Real.exp 1 * (σ ^ 2 + 1) := by
            gcongr
        _ = B * (η / (2 * (B + 1))) := by
            rw [hB]
            ring
        _ < η / 2 := hfrac hBnn hη
    set C := 2 / ε ^ 2 + |t| / ε + t ^ 2 / 2 with hCdef
    have hCnn : 0 ≤ C := by positivity
    have hCpos : (0 : ℝ) < C := by
      have : (0 : ℝ) < 2 / ε ^ 2 := by positivity
      positivity
    have hev_var : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ) < σ ^ 2 + 1 := by
      have h : ∀ᶠ n in atTop, dist (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ)
          (σ ^ 2) < 1 :=
        Filter.eventually_atTop.2 ((Metric.tendsto_atTop.mp hvar) 1 one_pos)
      filter_upwards [h] with n hn
      rw [dist_eq_norm, Real.norm_eq_abs, abs_lt] at hn
      linarith [hn.2]
    have hev_L : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n,
        ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ) <
          η / (2 * (C + 1)) := by
      have h := (hL ε hεpos).eventually
        (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < η / (2 * (C + 1))))
      filter_upwards [h] with n hn
      rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k _ => hLterm_nonneg n k ε)] at hn
      exact hn
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev_var
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev_L
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn_var := hN₁ n (le_trans (le_max_left _ _) hn)
    have hn_L := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
    calc ∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1 +
            (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖
        ≤ ∑ k ∈ Finset.range n, (|t| ^ 3 * ε * Real.exp 1 * (∫ ω, (X n k ω) ^ 2 ∂μ) +
            C * ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ) :=
          Finset.sum_le_sum fun k hk => hC ε hεpos hεt n k hk
      _ = |t| ^ 3 * ε * Real.exp 1 * (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ) +
            C * (∑ k ∈ Finset.range n,
              ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ < η / 2 + η / 2 := by
          apply add_lt_add
          · calc |t| ^ 3 * ε * Real.exp 1 * (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ)
                ≤ |t| ^ 3 * ε * Real.exp 1 * (σ ^ 2 + 1) :=
                  mul_le_mul_of_nonneg_left (le_of_lt hn_var) (by positivity)
              _ < η / 2 := hA1
          · calc C * (∑ k ∈ Finset.range n,
                    ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)
                ≤ C * (η / (2 * (C + 1))) :=
                  mul_le_mul_of_nonneg_left (le_of_lt hn_L) hCnn
              _ < η / 2 := hfrac hCnn hη
      _ = η := by ring
  -- Uniform smallness of `charFun - 1` across each row.
  have hv_unif : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ k ∈ Finset.range n,
      ‖charFun (μ.map (X n k)) t - 1‖ < η := by
    intro η hη
    set ε₂ := min (1 / |t|) (η / (4 * |t| + 1)) with hε₂
    have hε₂pos : 0 < ε₂ := lt_min (by positivity) (by positivity)
    have hε₂t : |t| * ε₂ ≤ 1 := by
      have hle : ε₂ ≤ 1 / |t| := min_le_left _ _
      calc |t| * ε₂ ≤ |t| * (1 / |t|) :=
            mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = 1 := mul_one_div_cancel (ne_of_gt (abs_pos.mpr ht))
    have h2t : 2 * |t| * ε₂ < η / 2 := by
      have h1 : ε₂ ≤ η / (4 * |t| + 1) := min_le_right _ _
      calc 2 * |t| * ε₂ ≤ 2 * |t| * (η / (4 * |t| + 1)) := by
            apply mul_le_mul_of_nonneg_left h1 (by positivity)
          _ < η / 2 := by
              rw [mul_div_assoc', div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * |t| + 1)]
              nlinarith [hη, abs_nonneg t, mul_pos hη (show (0 : ℝ) < 2 by norm_num)]
    have hevE := hE2_unif (η * ε₂ ^ 2 / 4) (by positivity)
    filter_upwards [hevE] with n hn k hk
    have hAmeas : MeasurableSet {ω | ε₂ < |X n k ω|} := by
      have h := measurableSet_lt (f := fun _ : Ω => ε₂) (g := fun ω => ‖X n k ω‖)
        measurable_const (hmeas n k hk).norm
      simpa [Real.norm_eq_abs] using h
    -- `charFun - 1` as an integral.
    have hv : charFun (μ.map (X n k)) t - 1 =
        ∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ := by
      rw [hchar n k hk]
      rw [show (∫ ω, (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ =
          ∫ ω, Complex.exp (↑t * ↑(X n k ω) * Complex.I) ∂μ -
            ∫ _ : Ω, (1 : ℂ) ∂μ) from
        integral_sub (hexp n k hk) (integrable_const (1 : ℂ))]
      simp
    have hfi : Integrable
        (fun ω => Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) μ :=
      (hexp n k hk).sub (integrable_const (1 : ℂ))
    rw [hv, ← integral_add_compl hAmeas hfi]
    have hsmall_part : ‖∫ ω in {ω | ε₂ < |X n k ω|}ᶜ,
        (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖ ≤ 2 * |t| * ε₂ := by
      calc ‖∫ ω in {ω | ε₂ < |X n k ω|}ᶜ,
              (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖
          ≤ ∫ ω in {ω | ε₂ < |X n k ω|}ᶜ, 2 * |t| * |X n k ω| ∂μ :=
            norm_integral_le_of_norm_le
              (((hX_int n k hk).abs.const_mul (2 * |t|)).integrableOn)
              (ae_restrict_of_forall_mem hAmeas.compl (fun ω hω => by
                have hXω : |X n k ω| ≤ ε₂ := by
                  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
                  exact hω
                have hz : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ ≤ 1 := by
                  have hzn : ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ = |t| * |X n k ω| := by
                    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
                      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
                      Real.norm_eq_abs]
                  rw [hzn]
                  calc |t| * |X n k ω| ≤ |t| * ε₂ :=
                        mul_le_mul_of_nonneg_left hXω (abs_nonneg _)
                    _ ≤ 1 := hε₂t
                calc ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1‖
                    ≤ 2 * ‖(↑t * ↑(X n k ω) * Complex.I : ℂ)‖ :=
                      Complex.norm_exp_sub_one_le hz
                  _ = 2 * |t| * |X n k ω| := by
                      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
                        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
                        Real.norm_eq_abs]
                      ring))
        _ ≤ ∫ ω in {ω | ε₂ < |X n k ω|}ᶜ, 2 * |t| * ε₂ ∂μ :=
            setIntegral_mono_on (((hX_int n k hk).abs.const_mul (2 * |t|)).integrableOn)
              (integrableOn_const) hAmeas.compl (fun ω hω => by
                have hXω : |X n k ω| ≤ ε₂ := by
                  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
                  exact hω
                exact mul_le_mul_of_nonneg_left hXω (by positivity))
        _ = 2 * |t| * ε₂ * μ.real {ω | ε₂ < |X n k ω|}ᶜ := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * |t| * ε₂ := by
            have h1 : μ.real {ω | ε₂ < |X n k ω|}ᶜ ≤ 1 := by
              have h2 : μ {ω | ε₂ < |X n k ω|}ᶜ ≤ 1 :=
                (measure_mono (Set.subset_univ _)).trans_eq measure_univ
              calc μ.real _ = (μ _).toReal := rfl
                _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h2
                _ = 1 := ENNReal.toReal_one
            calc 2 * |t| * ε₂ * μ.real {ω | ε₂ < |X n k ω|}ᶜ
                ≤ 2 * |t| * ε₂ * 1 := by
                  apply mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = 2 * |t| * ε₂ := by ring
    have hlarge_part : ‖∫ ω in {ω | ε₂ < |X n k ω|},
        (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖ ≤
          2 / ε₂ ^ 2 * (∫ ω, (X n k ω) ^ 2 ∂μ) := by
      have hμ : μ.real {ω | ε₂ < |X n k ω|} ≤
          (1 / ε₂ ^ 2) * ∫ ω, (X n k ω) ^ 2 ∂μ := by
        have h1 : ε₂ ^ 2 * μ.real {ω | ε₂ < |X n k ω|} ≤
            ∫ ω in {ω | ε₂ < |X n k ω|}, (X n k ω) ^ 2 ∂μ :=
          setIntegral_ge_of_const_le_real hAmeas (measure_ne_top μ _)
            (fun ω hω => by
              have hω' : ε₂ < |X n k ω| := hω
              have h := sq_le_sq' (a := ε₂) (b := |X n k ω|)
                (by linarith [abs_nonneg (X n k ω), hε₂pos.le]) (le_of_lt hω')
              rwa [sq_abs] at h)
            (hint2 n k hk).integrableOn
        have h2 : ∫ ω in {ω | ε₂ < |X n k ω|}, (X n k ω) ^ 2 ∂μ ≤
            ∫ ω, (X n k ω) ^ 2 ∂μ :=
          setIntegral_le_integral (hint2 n k hk)
            (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        calc μ.real {ω | ε₂ < |X n k ω|}
            ≤ (1 / ε₂ ^ 2) * (∫ ω in {ω | ε₂ < |X n k ω|}, (X n k ω) ^ 2 ∂μ) := by
              rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < ε₂ ^ 2)]
              have : μ.real {ω | ε₂ < |X n k ω|} * ε₂ ^ 2 =
                  ε₂ ^ 2 * μ.real {ω | ε₂ < |X n k ω|} := by ring
              rw [this, one_mul]
              exact h1
          _ ≤ (1 / ε₂ ^ 2) * ∫ ω, (X n k ω) ^ 2 ∂μ := by
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
      calc ‖∫ ω in {ω | ε₂ < |X n k ω|},
              (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖
          ≤ ∫ ω in {ω | ε₂ < |X n k ω|}, 2 ∂μ := by
            apply norm_integral_le_of_norm_le integrableOn_const
            apply ae_restrict_of_forall_mem hAmeas
            intro ω _
            calc ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1‖
                ≤ ‖Complex.exp (↑t * ↑(X n k ω) * Complex.I)‖ + 1 := by
                  simpa using norm_sub_le (Complex.exp (↑t * ↑(X n k ω) * Complex.I))
                    (1 : ℂ)
              _ = 2 := by
                  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
                  norm_num
        _ = 2 * μ.real {ω | ε₂ < |X n k ω|} := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * ((1 / ε₂ ^ 2) * ∫ ω, (X n k ω) ^ 2 ∂μ) := by
            exact mul_le_mul_of_nonneg_left hμ (by norm_num)
        _ = 2 / ε₂ ^ 2 * (∫ ω, (X n k ω) ^ 2 ∂μ) := by ring
    calc ‖∫ ω in {ω | ε₂ < |X n k ω|},
            (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ +
          ∫ ω in {ω | ε₂ < |X n k ω|}ᶜ,
            (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖
        ≤ ‖∫ ω in {ω | ε₂ < |X n k ω|},
            (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖ +
          ‖∫ ω in {ω | ε₂ < |X n k ω|}ᶜ,
            (Complex.exp (↑t * ↑(X n k ω) * Complex.I) - 1) ∂μ‖ := norm_add_le _ _
      _ ≤ 2 / ε₂ ^ 2 * (∫ ω, (X n k ω) ^ 2 ∂μ) + 2 * |t| * ε₂ :=
          add_le_add hlarge_part hsmall_part
      _ < η / 2 + η / 2 := by
          apply add_lt_add_of_le_of_lt
          · calc 2 / ε₂ ^ 2 * (∫ ω, (X n k ω) ^ 2 ∂μ)
                ≤ 2 / ε₂ ^ 2 * (η * ε₂ ^ 2 / 4) :=
                  mul_le_mul_of_nonneg_left (le_of_lt (hn k hk)) (by positivity)
              _ = η / 2 := by field_simp; ring
          · exact h2t
      _ = η := by ring
  -- The first-order terms are uniformly bounded in `L¹`, and their squares
  -- sum to `0`.
  have hVB : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n,
      ‖charFun (μ.map (X n k)) t - 1‖) ≤ (t ^ 2 / 2) * (σ ^ 2 + 1) + 1 := by
    have hev_var : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ) <
        σ ^ 2 + 1 := by
      have h : ∀ᶠ n in atTop, dist (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ)
          (σ ^ 2) < 1 :=
        Filter.eventually_atTop.2 ((Metric.tendsto_atTop.mp hvar) 1 one_pos)
      filter_upwards [h] with n hn
      rw [dist_eq_norm, Real.norm_eq_abs, abs_lt] at hn
      linarith [hn.2]
    have hev_e : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n,
        ‖charFun (μ.map (X n k)) t - 1 +
          (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖) < 1 := by
      have h := (hSumE.eventually
        (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)))
      filter_upwards [h] with n hn
      rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)] at hn
      exact hn
    filter_upwards [hev_var, hev_e] with n hn_var hn_e
    calc ∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖
        ≤ ∑ k ∈ Finset.range n, (‖charFun (μ.map (X n k)) t - 1 +
            (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ +
            (t ^ 2 / 2) * (∫ ω, (X n k ω) ^ 2 ∂μ)) := by
          apply Finset.sum_le_sum
          intro k _
          have htri : ‖charFun (μ.map (X n k)) t - 1‖ ≤
              ‖charFun (μ.map (X n k)) t - 1 +
                (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ +
              ‖(↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ := by
            have h := norm_add_le (charFun (μ.map (X n k)) t - 1 +
              (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ))
              (-((↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)))
            rw [add_neg_cancel_right, norm_neg] at h
            exact h
          calc ‖charFun (μ.map (X n k)) t - 1‖
              ≤ ‖charFun (μ.map (X n k)) t - 1 +
                  (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ +
                ‖(↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ := htri
            _ = ‖charFun (μ.map (X n k)) t - 1 +
                  (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖ +
                (t ^ 2 / 2) * (∫ ω, (X n k ω) ^ 2 ∂μ) := by
                congr 1
                rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
                  abs_of_nonneg (hE2_nonneg n k)]
      _ = (∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1 +
            (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)‖) +
          (t ^ 2 / 2) * (∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂μ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 1 + (t ^ 2 / 2) * (σ ^ 2 + 1) := by
          apply add_le_add (le_of_lt hn_e)
          exact mul_le_mul_of_nonneg_left (le_of_lt hn_var) (by positivity)
      _ = (t ^ 2 / 2) * (σ ^ 2 + 1) + 1 := by ring
  have hV2 : Tendsto (fun n => ∑ k ∈ Finset.range n,
      ‖charFun (μ.map (X n k)) t - 1‖ ^ 2) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    set B := (t ^ 2 / 2) * (σ ^ 2 + 1) + 1 with hBdef
    have hBpos : (0 : ℝ) < B := by
      have : (0 : ℝ) ≤ (t ^ 2 / 2) * (σ ^ 2 + 1) := by positivity
      linarith
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hVB
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hv_unif (δ / (B + 1))
      (by positivity))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hnB := hN₁ n (le_trans (le_max_left _ _) hn)
    have hnv := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    calc ∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖ ^ 2
        ≤ ∑ k ∈ Finset.range n,
            (δ / (B + 1)) * ‖charFun (μ.map (X n k)) t - 1‖ := by
          apply Finset.sum_le_sum
          intro k hk
          rw [sq]
          exact mul_le_mul_of_nonneg_right (le_of_lt (hnv k hk)) (norm_nonneg _)
      _ = (δ / (B + 1)) * (∑ k ∈ Finset.range n,
            ‖charFun (μ.map (X n k)) t - 1‖) := by rw [Finset.mul_sum]
      _ ≤ (δ / (B + 1)) * B := by
          exact mul_le_mul_of_nonneg_left hnB (by positivity)
      _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < B + 1)]
          nlinarith [hδ, hBpos]
  -- The product is close to the exponential of the sum of first-order terms.
  have hG : Tendsto (fun n => (∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t) -
      Complex.exp (∑ k ∈ Finset.range n, (charFun (μ.map (X n k)) t - 1)))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
    intro δ hδ
    set B := (t ^ 2 / 2) * (σ ^ 2 + 1) + 1 with hBdef
    have hev2 : ∀ᶠ n in atTop, (∑ k ∈ Finset.range n,
        ‖charFun (μ.map (X n k)) t - 1‖ ^ 2) * Real.exp B < δ := by
      have h := (Filter.Tendsto.mul_const (Real.exp B) hV2).eventually
        (Metric.ball_mem_nhds (0 * Real.exp B) hδ)
      filter_upwards [h] with n hn
      rw [zero_mul, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤
          (∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖ ^ 2) * Real.exp B)] at hn
      exact hn
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hv_unif (1 / 2) (by norm_num))
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hVB
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 hev2
    refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
    have hn1 := hN₁ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
    have hnB := hN₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have hn2 := hN₃ n (le_trans (le_max_right _ _) hn)
    have hprod : (∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t) =
        ∏ k ∈ Finset.range n, (1 + (charFun (μ.map (X n k)) t - 1)) := by
      apply Finset.prod_congr rfl
      intro k _
      ring
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hprod]
    calc ‖∏ k ∈ Finset.range n, (1 + (charFun (μ.map (X n k)) t - 1)) -
            Complex.exp (∑ k ∈ Finset.range n, (charFun (μ.map (X n k)) t - 1))‖
        ≤ (∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖ ^ 2) *
            Real.exp (∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖) :=
          prod_one_add_sub_exp_sum_le (Finset.range n) _
            (fun k hk => le_of_lt (hn1 k hk))
      _ ≤ (∑ k ∈ Finset.range n, ‖charFun (μ.map (X n k)) t - 1‖ ^ 2) *
            Real.exp B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          exact hnB
      _ < δ := hn2
  -- The exponential of the sum of first-order terms tends to the target.
  have hH : Tendsto (fun n => Complex.exp (∑ k ∈ Finset.range n,
      (charFun (μ.map (X n k)) t - 1)))
      atTop (𝓝 (Complex.exp (-(↑(σ ^ 2) * ↑t ^ 2 / 2)))) := by
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.range n,
        (charFun (μ.map (X n k)) t - 1)) atTop (𝓝 (-(↑(σ ^ 2) * ↑t ^ 2 / 2))) := by
      have hsum_e : Tendsto (fun n => ∑ k ∈ Finset.range n,
          (charFun (μ.map (X n k)) t - 1 +
            (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ))) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        apply squeeze_zero (fun n => norm_nonneg _)
        · intro n
          exact norm_sum_le _ _
        · exact hSumE
      have hsum_E2 : Tendsto (fun n => ∑ k ∈ Finset.range n,
          ((↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ))) atTop
          (𝓝 ((↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(σ ^ 2))) := by
        have hmul := Filter.Tendsto.mul_const (↑(t ^ 2 / 2 : ℝ) : ℂ)
          ((Complex.continuous_ofReal.tendsto _).comp hvar)
        have hsum_eq : (fun n => ∑ k ∈ Finset.range n,
            ((↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ))) =
            (fun n => (↑(∑ k ∈ Finset.range n, (∫ ω, (X n k ω) ^ 2 ∂μ)) : ℂ) *
              (↑(t ^ 2 / 2 : ℝ) : ℂ)) := by
          funext n
          have h1 : (↑(∑ k ∈ Finset.range n, (∫ ω, (X n k ω) ^ 2 ∂μ)) : ℂ) =
              ∑ k ∈ Finset.range n, (↑(∫ ω, (X n k ω) ^ 2 ∂μ) : ℂ) :=
            Complex.ofReal_sum _ _
          rw [h1, ← Finset.mul_sum]
          exact mul_comm _ _
        rw [hsum_eq]
        have hlim_eq : (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(σ ^ 2) =
            ↑(σ ^ 2) * (↑(t ^ 2 / 2 : ℝ) : ℂ) := mul_comm _ _
        rw [hlim_eq]
        exact hmul
      have hdiff : (fun n => ∑ k ∈ Finset.range n,
          (charFun (μ.map (X n k)) t - 1)) =
          (fun n => (∑ k ∈ Finset.range n,
            (charFun (μ.map (X n k)) t - 1 +
              (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ))) -
            (∑ k ∈ Finset.range n,
              ((↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(∫ ω, (X n k ω) ^ 2 ∂μ)))) := by
        funext n
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hdiff]
      have hlim : (0 : ℂ) - (↑(t ^ 2 / 2 : ℝ) : ℂ) * ↑(σ ^ 2) =
          -(↑(σ ^ 2) * ↑t ^ 2 / 2) := by
        push_cast
        ring
      rw [← hlim]
      exact hsum_e.sub hsum_E2
    exact (Complex.continuous_exp.tendsto _).comp hsum
  -- Combine: product = (product - exp sum) + exp sum.
  have hfinal : (fun n => ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t) =
      (fun n => ((∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t) -
        Complex.exp (∑ k ∈ Finset.range n, (charFun (μ.map (X n k)) t - 1))) +
        Complex.exp (∑ k ∈ Finset.range n, (charFun (μ.map (X n k)) t - 1))) := by
    funext n
    rw [sub_add_cancel]
  rw [hfinal]
  simpa using hG.add hH

/-- **Lindeberg–Feller central limit theorem** (triangular array form).

Suppose `X n k`, for `1 ≤ k ≤ n`, is a triangular array of independent,
mean-zero random variables on `(Ω, μ)`, square-integrable in the genuine
sense (`hint2`). If
* the row variances `∑ₖ 𝔼[X n k²]` converge to `σ² > 0`, and
* the Lindeberg condition `LindebergConditionTriangular X μ` holds,

then the row sums `Sₙ = ∑ₖ X n k` converge in distribution to `N(0, σ²)`:
for every bounded continuous `f : ℝ →ᵇ ℝ`,
`𝔼[f(Sₙ)] → 𝔼[f(σ · χ)]` where `χ` is a standard normal. -/
theorem lindeberg_feller_clt_triangular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (hind : ∀ n, iIndepFun (m := fun _ => inferInstance)
      ((Finset.range n).restrict (X n)) μ)
    (hmeas : ∀ n, ∀ k ∈ Finset.range n, Measurable (X n k))
    (hmean : ∀ n, ∀ k ∈ Finset.range n, ∫ ω, X n k ω ∂μ = 0)
    (hint2 : ∀ n, ∀ k ∈ Finset.range n, Integrable (fun ω => (X n k ω) ^ 2) μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : Tendsto (fun n => ∑ k ∈ Finset.range n,
              ∫ ω, (X n k ω) ^ 2 ∂μ) atTop (𝓝 (σ ^ 2)))
    (hL : LindebergConditionTriangular X μ) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(Measure.map (fun ω => ∑ k ∈ Finset.range n, X n k ω) μ))
        atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩))) := by
  let v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hv : (v : ℝ) = σ ^ 2 := rfl
  have hSn_meas : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range n, X n k ω) :=
    fun n => Finset.measurable_sum _ fun k hk => hmeas n k hk
  have hSn_prob : ∀ n,
      IsProbabilityMeasure (μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω)) :=
    fun n => ⟨by rw [Measure.map_apply (hSn_meas n) MeasurableSet.univ,
      Set.preimage_univ]; simp⟩
  let μn : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω), hSn_prob n⟩
  let μ₀ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 v, inferInstance⟩
  suffices h : Tendsto μn atTop (𝓝 μ₀) by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    exact h
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hcharFun_eq : ∀ n, charFun (↑(μn n)) t =
      ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t := by
    intro n
    show charFun (μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω)) t = _
    have h := (hind n).charFun_map_fun_finsetSum_eq_prod
      (fun i hi => (hmeas n i hi).aemeasurable)
    exact (congr_fun h t).trans (by simp [Finset.prod_apply])
  have hcharFun_target : charFun (↑μ₀) t =
      Complex.exp (-(↑(σ ^ 2) * ↑t ^ 2 / 2)) := by
    show charFun (gaussianReal 0 v) t = _
    rw [charFun_gaussianReal]
    have hvC : (v : ℂ) = ↑(σ ^ 2) := by exact_mod_cast hv
    rw [hvC]
    simp
  simp_rw [hcharFun_eq, hcharFun_target]
  exact lindeberg_charFun_product_tendsto X hmeas hmean hint2 σ hσ hvar hL t

end ProbabilityTheory
