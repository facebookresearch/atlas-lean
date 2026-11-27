/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianShift

/-!
# Randomized smoothing: the certified `ℓ²` radius

Randomized smoothing (Cohen, Rosenfeld and Kolter, 2019) turns a base classifier
`f : ℝⁿ → Y` into the smoothed classifier that predicts, at `x`, the class `c` maximizing
`P(f(x + ε) = c)` for Gaussian noise `ε ~ N(0, σ² I)`. Here `ℝⁿ` is
`EuclideanSpace ℝ ι`, the noise is `σ • Z` with `Z ~ stdGaussian`, and `Φ`, `Φ⁻¹` are the
standard normal cdf `cdf (gaussianReal 0 1)` and its generalized inverse
`cdfQuantile (gaussianReal 0 1)`. All probabilities are exact; nothing here estimates them.

## Main definitions

* `smoothedProb f σ x c = P(f(x + σ Z) = c)`, `Z ~ stdGaussian`.

## Main results

* `smoothedProb_eq_multivariateGaussian`: `smoothedProb f σ x c` is the `N(x, σ² I)` probability
  of `f ⁻¹' {c}` (Mathlib's `multivariateGaussian x (σ² • 1)`).
* `smoothedProb_lower`, `smoothedProb_upper`: the class probabilities at `x + δ` are bounded by
  `Φ(Φ⁻¹ p ∓ ‖δ‖ / σ)`, from the Gaussian Neyman–Pearson shift bounds
  `ProbabilityTheory.stdGaussian_shift_lower` and `ProbabilityTheory.stdGaussian_shift_upper`
  (Cohen et al., Lemma 4) in `MathlibExt.Probability.Distributions.GaussianShift`.
* `smoothedProb_lt_of_norm_lt` (Cohen et al., Theorem 1): if
  `p_A ≤ P(f(x + σZ) = a)` and `P(f(x + σZ) = c) ≤ p_B` for every `c ≠ a`, with
  `p_A, p_B ∈ (0, 1)`, then `a` is still the unique most probable class at `x + δ` whenever
  `‖δ‖ < σ / 2 * (Φ⁻¹ p_A - Φ⁻¹ p_B)`.
* `smoothedProb_lt_of_norm_lt_quantile`: the one-class form with `p_B = 1 - p_A`: the radius is
  `σ * Φ⁻¹ p_A`.

The endpoint `p_A = 1` (infinite radius) is excluded: `cdfQuantile` is totalized by `0` outside
`(0, 1)`, so it does not encode `Φ⁻¹ 1 = ∞`. Monte Carlo estimation of `p_A`, `p_B` and the
resulting failure probability are not covered.

## References

* J. Cohen, E. Rosenfeld and J. Z. Kolter, *Certified adversarial robustness via randomized
  smoothing*, ICML 2019, Theorem 1 and Lemma 4 (arXiv:1902.02918).
* J. Neyman and E. S. Pearson, *On the problem of the most efficient tests of statistical
  hypotheses*, Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Robustness

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-! ### Smoothed classifiers -/

variable {Y : Type*}

/-- The probability that the base classifier `f` returns `c` at `x + σ Z`, `Z ~ stdGaussian`:
the class probability of the randomized-smoothing classifier with noise `N(0, σ² I)`. -/
noncomputable def smoothedProb (f : EuclideanSpace ℝ ι → Y) (σ : ℝ) (x : EuclideanSpace ℝ ι)
    (c : Y) : ℝ :=
  (stdGaussian (EuclideanSpace ℝ ι)).real {z | f (x + σ • z) = c}

variable {f : EuclideanSpace ℝ ι → Y} {σ : ℝ}

/-- Moving the input by `δ` moves the noise by `σ⁻¹ δ`. -/
private theorem smoothedProb_add (hσ : σ ≠ 0) (x δ : EuclideanSpace ℝ ι) (c : Y) :
    smoothedProb f σ (x + δ) c =
      (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + σ⁻¹ • δ ∈ {w | f (x + σ • w) = c}} := by
  unfold smoothedProb
  congr 1
  ext z
  simp only [mem_ofPred_eq, smul_add, smul_inv_smul₀ hσ]
  rw [add_right_comm, add_assoc x]

private theorem norm_inv_smul (hσ : 0 < σ) (δ : EuclideanSpace ℝ ι) : ‖σ⁻¹ • δ‖ = ‖δ‖ / σ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hσ, inv_mul_eq_div]

variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- `smoothedProb f σ x c` is the probability that `f(X) = c` for `X ~ N(x, σ² I)`. -/
theorem smoothedProb_eq_multivariateGaussian [DecidableEq ι] (hf : Measurable f)
    (x : EuclideanSpace ℝ ι) (c : Y) :
    smoothedProb f σ x c =
      (multivariateGaussian x (σ ^ 2 • (1 : Matrix ι ι ℝ))).real (f ⁻¹' {c}) := by
  rw [← stdGaussian_map_const_add_smul,
    map_measureReal_apply (by fun_prop) (hf (measurableSet_singleton c))]
  rfl

private theorem measurableSet_smoothed {E : Type*} [MeasurableSpace E] [Add E] [SMul ℝ E]
    [MeasurableAdd E] [MeasurableConstSMul ℝ E] {g : E → Y} (hg : Measurable g) (σ : ℝ) (x : E)
    (c : Y) : MeasurableSet {z : E | g (x + σ • z) = c} :=
  (hg.comp ((measurable_const_add x).comp (measurable_const_smul σ))) (measurableSet_singleton c)

/-- Lower bound on the smoothed class probability at a perturbed input. -/
theorem smoothedProb_lower (hf : Measurable f) (hσ : 0 < σ) {x : EuclideanSpace ℝ ι} {c : Y}
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : p ≤ smoothedProb f σ x c) (δ : EuclideanSpace ℝ ι) :
    cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) p - ‖δ‖ / σ) ≤
      smoothedProb f σ (x + δ) c := by
  rw [smoothedProb_add hσ.ne', ← norm_inv_smul hσ]
  exact stdGaussian_shift_lower (measurableSet_smoothed hf σ x c) _ hp h

/-- Upper bound on the smoothed class probability at a perturbed input. -/
theorem smoothedProb_upper (hf : Measurable f) (hσ : 0 < σ) {x : EuclideanSpace ℝ ι} {c : Y}
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : smoothedProb f σ x c ≤ p) (δ : EuclideanSpace ℝ ι) :
    smoothedProb f σ (x + δ) c ≤
      cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) p + ‖δ‖ / σ) := by
  rw [smoothedProb_add hσ.ne', ← norm_inv_smul hσ]
  exact stdGaussian_shift_upper (measurableSet_smoothed hf σ x c) _ hp h

/-- **Certified `ℓ²` radius of randomized smoothing** (Cohen et al., Theorem 1). Let
`p_A ≤ P(f(x + σZ) = a)` and `P(f(x + σZ) = c) ≤ p_B` for every `c ≠ a`, with
`p_A, p_B ∈ (0, 1)` and `σ > 0`. Then for every `δ` with
`‖δ‖ < σ / 2 * (Φ⁻¹ p_A - Φ⁻¹ p_B)`, the class `a` is strictly more probable than every other
class at `x + δ`: the smoothed classifier still predicts `a`. -/
theorem smoothedProb_lt_of_norm_lt (hf : Measurable f) (hσ : 0 < σ) {x : EuclideanSpace ℝ ι}
    {a : Y} {pA pB : ℝ} (hpA : pA ∈ Ioo (0 : ℝ) 1) (hpB : pB ∈ Ioo (0 : ℝ) 1)
    (hA : pA ≤ smoothedProb f σ x a) (hB : ∀ c, c ≠ a → smoothedProb f σ x c ≤ pB)
    {δ : EuclideanSpace ℝ ι}
    (hδ : ‖δ‖ < σ / 2 * (cdfQuantile (gaussianReal 0 1) pA - cdfQuantile (gaussianReal 0 1) pB))
    {c : Y} (hc : c ≠ a) :
    smoothedProb f σ (x + δ) c < smoothedProb f σ (x + δ) a := by
  have hr : ‖δ‖ / σ <
      (cdfQuantile (gaussianReal 0 1) pA - cdfQuantile (gaussianReal 0 1) pB) / 2 := by
    rw [div_lt_iff₀ hσ]
    linarith
  calc smoothedProb f σ (x + δ) c
      ≤ cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) pB + ‖δ‖ / σ) :=
        smoothedProb_upper hf hσ hpB (hB c hc) δ
    _ < cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) pA - ‖δ‖ / σ) :=
        strictMono_cdf_gaussianReal 0 one_ne_zero (by linarith)
    _ ≤ smoothedProb f σ (x + δ) a := smoothedProb_lower hf hσ hpA hA δ

/-- **Certified radius `σ Φ⁻¹(p_A)`**: the one-class form of `smoothedProb_lt_of_norm_lt`. If
`p_A ≤ P(f(x + σZ) = a)` with `p_A ∈ (0, 1)`, then every other class has probability at most
`1 - p_A`, and `a` stays the strictly most probable class at `x + δ` for every
`‖δ‖ < σ * Φ⁻¹ p_A`. The radius is positive exactly when `p_A > 1/2`. -/
theorem smoothedProb_lt_of_norm_lt_quantile (hf : Measurable f) (hσ : 0 < σ)
    {x : EuclideanSpace ℝ ι} {a : Y} {pA : ℝ} (hpA : pA ∈ Ioo (0 : ℝ) 1)
    (hA : pA ≤ smoothedProb f σ x a) {δ : EuclideanSpace ℝ ι}
    (hδ : ‖δ‖ < σ * cdfQuantile (gaussianReal 0 1) pA) {c : Y} (hc : c ≠ a) :
    smoothedProb f σ (x + δ) c < smoothedProb f σ (x + δ) a := by
  have hpB : 1 - pA ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hpA.2], by linarith [hpA.1]⟩
  refine smoothedProb_lt_of_norm_lt hf hσ hpA hpB hA (fun c' hc' => ?_) ?_ hc
  · have hsub : {z : EuclideanSpace ℝ ι | f (x + σ • z) = c'} ⊆
        {z | f (x + σ • z) = a}ᶜ := fun z hz hza => hc' (hz.symm.trans hza)
    have := measureReal_mono (μ := stdGaussian (EuclideanSpace ℝ ι)) hsub
    rw [measureReal_compl (measurableSet_smoothed hf σ x a), probReal_univ] at this
    unfold smoothedProb at hA ⊢
    linarith
  · rw [cdfQuantile_gaussianReal_one_sub]
    linarith

end Cslib.MachineLearning.Robustness
