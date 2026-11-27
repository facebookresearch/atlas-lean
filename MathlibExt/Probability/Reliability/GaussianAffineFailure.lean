/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import MathlibExt.Analysis.Calculus.HessianCertificate
import MathlibExt.Probability.Reliability.FailureBracket

/-!
# Gaussian affine failure bracket

For a standard Gaussian `Z` on `EuclideanSpace ℝ (Fin n)` and a
nonzero continuous linear functional `L`, the affine failure
probability `P(a + L Z ≤ t)` is the standard normal cdf at
`(t - a) / ‖L‖`. Combining that standardization with a
remainder bound for `g` against its affine model on a closed
ball brackets `P(g(Z) ≤ 0)` by the shifted affine probabilities,
up to the Gaussian mass outside the ball. The Hessian
specialization supplies the remainder bound
`M * R^2 / 2` for the first-order model at the origin.

## Main results

* `Reliability.stdGaussian_affine_le_measure`: the affine
  standard-Gaussian half-space law.
* `Reliability.stdGaussian_affine_failure_bracket`: the
  combined bracket from a ball remainder bound.
* `Reliability.stdGaussian_hessian_failure_bracket`: the
  Hessian-certificate specialization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Reliability

/-- Affine half-space probability for the standard Gaussian on
`EuclideanSpace ℝ (Fin n)`.

For a nonzero continuous linear functional `L`, the affine
variable `a + L Z`, with `Z` standard Gaussian, has Gaussian law
with mean `a` and standard deviation `‖L‖`; hence
`P(a + L Z ≤ t) = Φ((t - a) / ‖L‖)`, where `Φ` is the standard
normal cdf. This is the Euclidean dual-norm form: the variance
is the squared operator norm of `L`, not a coordinate sup norm. -/
theorem stdGaussian_affine_le_measure {n : ℕ}
    {L : StrongDual ℝ (EuclideanSpace ℝ (Fin n))} (hL : L ≠ 0)
    (a t : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) {z | a + L z ≤ t}
      = ENNReal.ofReal
          (cdf (gaussianReal 0 1) ((t - a) / ‖L‖)) := by
  have hσ : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hσne : (‖L‖ : ℝ) ≠ 0 := ne_of_gt hσ
  have hLmeas : Measurable (⇑L : EuclideanSpace ℝ (Fin n) → ℝ) :=
    L.continuous.measurable
  have hmapL : (stdGaussian (EuclideanSpace ℝ (Fin n))).map (⇑L)
      = gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
  have hXmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) => a + L z) :=
    (measurable_const.add hLmeas)
  have hameas : Measurable (fun x : ℝ => a + x) := measurable_const.add measurable_id
  have hcomp : (fun z : EuclideanSpace ℝ (Fin n) => a + L z)
      = (fun x : ℝ => a + x) ∘ (⇑L) := rfl
  have hset : {z : EuclideanSpace ℝ (Fin n) | a + L z ≤ t}
      = (fun z : EuclideanSpace ℝ (Fin n) => a + L z) ⁻¹' (Iic t) := rfl
  rw [hset, ← Measure.map_apply hXmeas measurableSet_Iic, hcomp,
    ← Measure.map_map hameas hLmeas, hmapL, gaussianReal_map_const_add, zero_add,
    ofReal_cdf]
  have hfmeas : Measurable (fun x : ℝ => (x - a) / ‖L‖) :=
    (measurable_id.sub measurable_const).div_const _
  have hpre : (fun x : ℝ => (x - a) / ‖L‖) ⁻¹' (Iic ((t - a) / ‖L‖)) = Iic t := by
    ext x
    simp only [mem_preimage, mem_Iic]
    rw [div_le_iff₀ hσ, div_mul_cancel₀ _ hσne, sub_le_sub_iff_right]
  have hvar : (‖L‖ ^ 2).toNNReal / NNReal.mk (‖L‖ ^ 2) (sq_nonneg _) = 1 := by
    rw [Real.toNNReal_of_nonneg (sq_nonneg _)]
    refine div_self ?_
    rw [ne_eq, ← NNReal.coe_eq_zero, NNReal.coe_mk]
    exact pow_ne_zero 2 hσne
  have hdivmeas : Measurable (fun x : ℝ => x / ‖L‖) := measurable_id.div_const _
  have hsubmeas : Measurable (fun x : ℝ => x - a) := measurable_id.sub measurable_const
  have hmapf : (gaussianReal a (‖L‖ ^ 2).toNNReal).map (fun x : ℝ => (x - a) / ‖L‖)
      = gaussianReal 0 1 := by
    have hfcomp : (fun x : ℝ => (x - a) / ‖L‖)
        = (fun x : ℝ => x / ‖L‖) ∘ (fun x : ℝ => x - a) := rfl
    rw [hfcomp, ← Measure.map_map hdivmeas hsubmeas,
      gaussianReal_map_sub_const, sub_self, gaussianReal_map_div_const, zero_div, hvar]
  rw [← hpre, ← Measure.map_apply hfmeas measurableSet_Iic, hmapf]

/-- Combined Gaussian affine failure bracket.

If on the closed radius-`R` ball the limit-state function `g`
differs from its affine model `z ↦ a + L z` by at most `delta`,
then the standard-Gaussian failure probability `P(g(Z) ≤ 0)` is
bracketed by the shifted affine Gaussian probabilities, up to
the Gaussian mass outside the ball. The nonzero-functional
hypothesis is essential: at `L = 0` the affine law is degenerate
and the displayed standardization has no meaning. -/
theorem stdGaussian_affine_failure_bracket {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : StrongDual ℝ (EuclideanSpace ℝ (Fin n))} (hL : L ≠ 0)
    {a R delta : ℝ}
    (hrem : ∀ z ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) R,
      |g z - (a + L z)| ≤ delta) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
        ≤ ENNReal.ofReal
            (cdf (gaussianReal 0 1) ((delta - a) / ‖L‖))
          + stdGaussian (EuclideanSpace ℝ (Fin n))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ
      ∧ ENNReal.ofReal
            (cdf (gaussianReal 0 1) ((-delta - a) / ‖L‖))
        ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
          + stdGaussian (EuclideanSpace ℝ (Fin n))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  constructor
  · calc stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
        ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {z | a + L z ≤ delta}
            + stdGaussian (EuclideanSpace ℝ (Fin n)) (Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
          measure_failure_bracket_upper
            (stdGaussian (EuclideanSpace ℝ (Fin n))) g
            (fun z => a + L z)
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
            delta hrem
      _ = ENNReal.ofReal (cdf (gaussianReal 0 1) ((delta - a) / ‖L‖))
            + stdGaussian (EuclideanSpace ℝ (Fin n)) (Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
          rw [stdGaussian_affine_le_measure hL a delta]
  · calc ENNReal.ofReal (cdf (gaussianReal 0 1) ((-delta - a) / ‖L‖))
        = stdGaussian (EuclideanSpace ℝ (Fin n)) {z | a + L z ≤ -delta} := by
          rw [stdGaussian_affine_le_measure hL a (-delta)]
      _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
            + stdGaussian (EuclideanSpace ℝ (Fin n)) (Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
          measure_failure_bracket_lower
            (stdGaussian (EuclideanSpace ℝ (Fin n))) g
            (fun z => a + L z)
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
            delta hrem

/-- Hessian-certificate form of the Gaussian affine failure
bracket: if `g` is `C²` on the closed radius-`R` ball with
Hessian operator norm at most `M`, and the derivative functional
at the origin is nonzero, then the standard-Gaussian failure
probability is bracketed by the affine first-order model shifted
by `M * R^2 / 2`, up to the mass outside the ball. -/
theorem stdGaussian_hessian_failure_bracket {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (hC2 : ∀ y ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) R,
      ContDiffAt ℝ 2 g y)
    (hH : ∀ y ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M)
    (hderiv : fderiv ℝ g 0 ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
        ≤ ENNReal.ofReal
            (cdf (gaussianReal 0 1)
              ((M * R ^ 2 / 2 - g 0) / ‖fderiv ℝ g 0‖))
          + stdGaussian (EuclideanSpace ℝ (Fin n))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ
      ∧ ENNReal.ofReal
            (cdf (gaussianReal 0 1)
              ((-(M * R ^ 2 / 2) - g 0) / ‖fderiv ℝ g 0‖))
        ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {z | g z ≤ 0}
          + stdGaussian (EuclideanSpace ℝ (Fin n))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
  stdGaussian_affine_failure_bracket hderiv
    (fun _z hz => hessian_error_certificate hR hC2 hH hz)

end Reliability
