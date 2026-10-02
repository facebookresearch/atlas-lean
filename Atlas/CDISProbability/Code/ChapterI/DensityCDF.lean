/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# CDIS Probabilités I: distribution function of a law with density

* id 28 (1): if `X` has a density, its distribution function `F` is continuous, and
  `P(X = x) = 0` for every `x`.
* id 28 (2): `F` is differentiable at every point `x` where the density `f` is continuous, with
  `F'(x) = f(x)`.
* id 28 (3): conversely, if `F` is continuous everywhere and differentiable outside a countable
  set (in particular, piecewise differentiable), then the law has density `F'`.

Part (3) uses the fundamental theorem of calculus with a countable exceptional set
(`integral_eq_of_hasDerivAt_off_countable`) and the integrability of the derivative of a
monotone function (`MonotoneOn.intervalIntegrable_deriv`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace CDIS

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- CDIS P.I, id 28 (1): a law without atoms has a continuous distribution function. -/
theorem continuous_cdf_of_measure_singleton (h0 : ∀ x, μ {x} = 0) : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim, (cdf μ).rightLim_eq]
  have hs := (cdf μ).measure_singleton x
  rw [measure_cdf, h0 x] at hs
  have hle := (monotone_cdf μ).leftLim_le (le_refl x)
  have : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.1 hs.symm
  linarith

/-- CDIS P.I, id 28 (1): a law with a density has no atoms and a continuous distribution
function. -/
theorem measure_singleton_and_continuous_cdf (hμ : μ ≪ volume) :
    (∀ x, μ {x} = 0) ∧ Continuous (cdf μ) :=
  ⟨fun _ ↦ hμ Real.volume_singleton,
    continuous_cdf_of_measure_singleton fun _ ↦ hμ Real.volume_singleton⟩

variable {f : ℝ → ℝ}

/-- For a law with density `f`, `F(y) = ∫_{-∞}^y f`. -/
lemma cdf_withDensity_eq (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    [IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (f x))] (y : ℝ) :
    cdf (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) y = ∫ t in Iic y, f t := by
  rw [cdf_eq_real, Measure.real, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (Eventually.of_forall hf0),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun t _ ↦ hf0 t)]

/-- CDIS P.I, id 28 (2): `F'(x) = f(x)` at every point where `f` is continuous. -/
theorem hasDerivAt_cdf_withDensity (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) (hfi : Integrable f)
    [IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (f x))] {x : ℝ}
    (hc : ContinuousAt f x) :
    HasDerivAt (cdf (volume.withDensity fun x ↦ ENNReal.ofReal (f x))) (f x) x := by
  have key : (cdf (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) : ℝ → ℝ) =
      fun y ↦ (∫ t in Iic (x - 1), f t) + ∫ t in (x - 1)..y, f t := by
    funext y
    rw [cdf_withDensity_eq hf0 hfi, ← intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn
      hfi.integrableOn]
    ring
  rw [key]
  exact (intervalIntegral.integral_hasDerivAt_right hfi.intervalIntegrable
    hfm.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_add _

/-- CDIS P.I, id 28 (3): if the distribution function is continuous and differentiable outside a
countable set, the law has density `F'`. -/
theorem eq_withDensity_deriv_cdf (hcont : Continuous (cdf μ)) {s : Set ℝ} (hs : s.Countable)
    (hd : ∀ x ∉ s, DifferentiableAt ℝ (cdf μ) x) :
    μ = volume.withDensity fun x ↦ ENNReal.ofReal (deriv (cdf μ) x) := by
  have hmono := monotone_cdf μ
  have hFTC : ∀ a b : ℝ, a ≤ b → ∫ t in a..b, deriv (cdf μ) t = cdf μ b - cdf μ a :=
    fun a b _ ↦ integral_eq_of_hasDerivAt_off_countable _ _ hs hcont.continuousOn
      (fun x hx ↦ (hd x hx.2).hasDerivAt) (hmono.monotoneOn _).intervalIntegrable_deriv
  refine Measure.ext_of_Ioc' μ _ (fun _ _ _ ↦ measure_ne_top μ _) fun a b hab ↦ ?_
  have hint : IntegrableOn (deriv (cdf μ)) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1
      (hmono.monotoneOn _).intervalIntegrable_deriv
  conv_lhs => rw [← measure_cdf μ]
  rw [StieltjesFunction.measure_Ioc, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ hmono.deriv_nonneg),
    ← intervalIntegral.integral_of_le hab.le, hFTC a b hab.le]

end CDIS
