/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoDensity
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Tests for the density of elementary integrands

Non-vacuity of the density theorem and of the progressive isometry on the constant integrand `1`
(which gives `E[(∫_0^t 1 dB)²] = t`), the boundary time `t = 0` (every progressive integrand is
Itô-approximable on `[0, 0]`), the first coefficient and the level-`0` truncation of the
delayed-average approximation, Lebesgue differentiation along the delayed windows
`[u - 2/(n+1), u - 1/(n+1)]`, and the isometry and martingale statements in the form recorded in
the wanted file (Brownian motion hypothesis `IsBrownianReal`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.ItoDensity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The constant integrand `1` has `E ∫_0^t 1² du = t P(Ω)`. -/
theorem lintegral_one (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖(fun (_ : ℝ≥0) (_ : Ω) ↦ (1 : ℝ)) u.toNNReal ω‖ₑ ^ 2) ∂P =
      ENNReal.ofReal t * P Set.univ := by
  simp

/-- Non-vacuity of the density theorem: the constant integrand `1` is Itô-approximable. -/
example [IsFiniteMeasure P] (t : ℝ≥0) : IsItoApproximable P F (fun _ _ ↦ (1 : ℝ)) t :=
  isItoApproximable_of_isProgressive (isProgressive_const F 1) t
    (by rw [lintegral_one]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))

/-- The progressive Itô isometry on the constant integrand: `E[(∫_0^t 1 dB)²] = t`. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    ∫⁻ ω, ‖itoIntegral P F B (fun _ _ ↦ 1) t ω‖ₑ ^ 2 ∂P = ENNReal.ofReal t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  rw [lintegral_itoIntegral_sq_of_isProgressive hB hBF hInd (isProgressive_const F 1) t
    (by rw [lintegral_one]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    lintegral_one, measure_univ, mul_one]

/-- Boundary time: every progressive integrand is Itô-approximable on `[0, 0]`, with no
integrability hypothesis (the time interval `(0, 0]` is empty). -/
example [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) :
    IsItoApproximable P F H 0 :=
  isItoApproximable_of_isProgressive hH 0 (by simp)

/-- The delayed-average approximation vanishes on its first interval `(0, t / (n + 1)]`. -/
example {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (M : ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    (delayedAverage hH M t n).coeff ⟨0, Nat.succ_pos n⟩ ω = 0 := by
  simp [delayedAverage]

/-- Truncating at level `0` gives the zero approximation (all coefficients vanish). -/
example {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0) (n : ℕ)
    (i : Fin (delayedAverage hH 0 t n).n) (ω : Ω) :
    (delayedAverage hH 0 t n).coeff i ω = 0 := by
  simp [delayedAverage, truncation_zero]

/-- Lebesgue differentiation along the delayed windows `[u - 2/(n+1), u - 1/(n+1)]`, which do not
contain `u`. -/
example {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ u : ℝ, Tendsto (fun n : ℕ ↦ ⨍ x in Set.Icc (u - 2 / (n + 1)) (u - 1 / (n + 1)), f x) atTop
      (𝓝 (f u)) := by
  filter_upwards [hf.ae_tendsto_average_Icc] with u hu
  have hlen : ∀ n : ℕ, u - 1 / ((n : ℝ) + 1) - (u - 2 / ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    intro n; ring
  refine hu _ _ (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ ?_) ?_
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hlen n]
  · rw [hlen]
    have e : u - (u - 2 / ((n : ℝ) + 1) + (u - 1 / ((n : ℝ) + 1))) / 2 =
        (3 / 2) * (1 / ((n : ℝ) + 1)) := by ring
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [e, abs_of_pos (by positivity)]
    linarith
  · simp_rw [hlen]
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The Itô isometry in the form recorded in the wanted file (Brownian motion hypothesis). -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P :=
  lintegral_itoIntegral_sq_of_isProgressive hB.toIsPreBrownianReal hBF hInd hH t hH2

/-- The martingale property in the form recorded in the wanted file (Brownian motion
hypothesis). -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    Martingale (itoIntegral P F B H) F P :=
  martingale_itoIntegral_of_isProgressive hB.toIsPreBrownianReal hBF hInd hH hH2

#print axioms isItoApproximable_of_isProgressive
#print axioms martingale_itoIntegral_of_isProgressive

end MathlibExtTest.Probability.ItoDensity
