/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import MathlibExt.Analysis.LaplaceTransform.Basic

/-!
# The one-sided Laplace transform as a damped Fourier transform

See M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*,
Cambridge University Press, free version v1.1 (2014), [§4.4.6, Definition 4.12 and
(4.90), p. 379](https://fourierandwavelets.org/FSP_v1.1_2014.pdf#page=370).
We adapt the two-sided identity by extending the damped signal by zero off `(0, ∞)`
and put `ω = 2πξ` to pass from angular frequency to Mathlib's Fourier convention.
The scalar formula extends to the Bochner integral in a complex Banach space.
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform Real

namespace MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If the zero extension `g` of `t ↦ exp (-σ * t) • f t` from `(0, ∞)` is integrable,
then the one-sided Laplace transform converges at each `σ + (2πξ)i` with value `𝓕 g ξ`.
On this line, it is bounded by the `L¹` norm of `g` and continuous in the real frequency `ξ`.
This is an identity on the line itself, not a limit from a half-plane. -/
theorem hasLaplace_damped_fourier [CompleteSpace E] {f : ℝ → E} {σ : ℝ}
    (hf : Integrable ((Set.Ioi 0).indicator (fun t : ℝ ↦ Real.exp (-σ * t) • f t))) :
    let g := (Set.Ioi 0).indicator (fun t : ℝ ↦ Real.exp (-σ * t) • f t)
    let s (ξ : ℝ) := (σ : ℂ) + ↑(2 * π * ξ) * Complex.I
    (∀ ξ : ℝ, HasLaplace f (s ξ) (𝓕 g ξ)) ∧
      (∀ ξ : ℝ, ‖laplace f (s ξ)‖ ≤ ∫ t : ℝ, ‖g t‖) ∧
      Continuous (fun ξ : ℝ ↦ laplace f (s ξ)) := by
  intro g s
  have hg : Integrable g := hf
  have hξ (ξ : ℝ) : HasLaplace f (s ξ) (𝓕 g ξ) := by
    have hkernel : (fun t : ℝ ↦ 𝐞 (-(t * ξ)) • g t) =
        (Set.Ioi 0).indicator (fun t : ℝ ↦ Complex.exp (-s ξ * (t : ℂ)) • f t) := by
      funext t
      by_cases ht : t ∈ Set.Ioi (0 : ℝ)
      · simp only [g, Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply,
          ← Complex.coe_smul, Complex.ofReal_exp, smul_smul, ← Complex.exp_add]
        congr 2
        dsimp only [s]
        push_cast
        ring
      · simp only [g, Set.indicator_of_notMem ht, smul_zero]
    refine ⟨?_, ?_⟩
    · have hi : Integrable (fun t : ℝ ↦ 𝐞 (-(t * ξ)) • g t) := by
        simpa only [Real.inner_apply] using (Real.fourierIntegral_convergent_iff ξ).2 hg
      rw [hkernel, integrable_indicator_iff measurableSet_Ioi] at hi
      exact hi
    · rw [laplace, Real.fourier_real_eq, hkernel, integral_indicator measurableSet_Ioi]
  refine ⟨hξ, fun ξ ↦ ?_, ?_⟩
  · rw [(hξ ξ).2]
    exact Real.norm_fourier_le_integral_norm g ξ
  · rw [show (fun ξ : ℝ ↦ laplace f (s ξ)) = 𝓕 g from funext fun ξ ↦ (hξ ξ).2]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg

end MetaMathlibExt
