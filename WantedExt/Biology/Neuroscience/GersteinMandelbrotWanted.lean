/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gerstein–Mandelbrot: a perfect integrator with Brownian input fires at inverse-Gaussian times

Gerstein and Mandelbrot (1964) model the membrane state of a neuron between spikes as a random
walk towards an absorbing threshold. In the diffusion limit, with drift `c` towards the
threshold and diffusion coefficient `1` (their normalization, so the displacement after time
`t` has variance `2t`), started at distance `z₀ > 0` from the threshold, the interspike interval
is the first passage time of `c t + √2 B(t)` to level `z₀`, for a standard Brownian motion `B`.
Its density is the inverse Gaussian
`I(T) = z₀ (4π)^{-1/2} T^{-3/2} exp(-(z₀ - cT)² / (4T))` for `T > 0`; for `c = 0` this is the
Lévy (stable index `1/2`) density. For `c < 0` the density has total mass below one (the
threshold may never be reached). After each spike the state is reset, so successive intervals
are independent copies; that renewal structure is not restated here.

The deterministic leaky integrate-and-fire first hit is
`Domains.Biology.Biophysics.IntegrateAndFire.FirstHit`; no first-passage law of Brownian motion
is on main.

Sources: G. L. Gerstein and B. Mandelbrot, "Random walk models for the spike activity of a single
neuron", Biophys. J. 4 (1964) 41–68.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.GersteinMandelbrotWanted

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **interspike interval**: the first time `t ≥ 0` at which the displacement `c t + √2 B(t)`
towards the threshold reaches the initial distance `z₀` (`0` if it is never reached). -/
noncomputable def firstPassageTime (z₀ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | z₀ ≤ c * t + √2 * B t ω}

/-- The **inverse Gaussian density** `z₀ (4π)^{-1/2} T^{-3/2} exp(-(z₀ - cT)² / (4T))`. -/
noncomputable def isiDensity (z₀ c T : ℝ) : ℝ :=
  z₀ / √(4 * π) * T ^ (-(3 / 2 : ℝ)) * exp (-(z₀ - c * T) ^ 2 / (4 * T))

/-- **Gerstein–Mandelbrot interspike-interval law** (Gerstein and Mandelbrot 1964). Let `P` be a
probability measure, `B` a standard real Brownian motion under `P` (`IsBrownianReal B P`),
`z₀ > 0` the distance to threshold and `c ∈ ℝ` the drift towards it. Then for all real `a, b`
with `0 < a ≤ b`, the probability that the first passage time of `c t + √2 B(t)` to `z₀` lies in
`[a, b]` equals `∫_a^b z₀ (4π)^{-1/2} T^{-3/2} exp(-(z₀ - cT)² / (4T)) dT`.

Source: Gerstein and Mandelbrot (1964). -/
public theorem_wanted measure_firstPassageTime_mem_Icc (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (z₀ c : ℝ) (hz₀ : 0 < z₀) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    P {ω | (firstPassageTime z₀ c B ω : ℝ) ∈ Set.Icc a b} =
      ENNReal.ofReal (∫ T in a..b, isiDensity z₀ c T)

end WantedExt.Biology.Neuroscience.GersteinMandelbrotWanted
