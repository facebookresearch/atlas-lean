/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Siegert formula: mean firing time of the noisy leaky integrate-and-fire neuron

The subthreshold voltage of a leaky integrate-and-fire neuron driven by white noise is the
Ornstein–Uhlenbeck process `τ dV = (μ - V) dt + σ √τ dW`, reset to `V₀ < θ` after each spike.
Siegert's formula gives the mean first passage time from `V₀` to the threshold `θ`:
`T = τ √π ∫_{(V₀-μ)/σ}^{(θ-μ)/σ} e^{u²} (1 + erf u) du`. With a refractory period `T_r`, the
stationary firing rate of the renewal spike train is `1 / (T_r + T)`; that renewal step is not
restated here.

The voltage is written as `V(t) = μ + (V₀ - μ) e^{-t/τ} + X(t)`, where `X` is an
Ornstein–Uhlenbeck process started at `0` with rate `1/τ` and noise amplitude `σ / √τ`
(`ProbabilityTheory.IsOrnsteinUhlenbeckFromZero` in `MathlibExt.Probability.OrnsteinUhlenbeck`,
which fixes the finite-dimensional laws), with continuous paths. The deterministic leaky
integrate-and-fire first hit is `Domains.Biology.Biophysics.IntegrateAndFire.FirstHit`.

Sources: A. J. F. Siegert, "On the first passage time probability problem", Phys. Rev. 81
(1951) 617–623; "Mean time-to-fire for the noisy LIF neuron: a detailed derivation of the
Siegert formula", arXiv:1501.04032.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Process.HittingTime
public import MathlibExt.Probability.OrnsteinUhlenbeck
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.SiegertFormulaWanted

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **error function** `erf u = (2/√π) ∫_0^u e^{-s²} ds`. -/
noncomputable def erf (u : ℝ) : ℝ :=
  2 / √π * ∫ s in (0 : ℝ)..u, exp (-s ^ 2)

/-- **Siegert's mean firing time.** The integral
`τ √π ∫_{(V₀-μ)/σ}^{(θ-μ)/σ} e^{u²} (1 + erf u) du` of all real `τ`, `μ`, `σ`, `V₀` and `θ`. It is
the mean firing time on the domain of `integral_firingTime`: `τ > 0`, `σ > 0` and `V₀ < θ`.
Outside that domain it need not be a time: for `τ > 0`, `σ > 0` and `V₀ > θ` the integrand is
positive and the bounds are reversed, so the value is negative. -/
noncomputable def siegertTime (τ μ σ V₀ θ : ℝ) : ℝ :=
  τ * √π * ∫ u in (V₀ - μ) / σ..(θ - μ) / σ, exp (u ^ 2) * (1 + erf u)

/-- **Membrane voltage**: `V(t, ω) = μ + (V₀ - μ) e^{-t/τ} + X(t, ω)`. In general
`V(0, ω) = V₀ + X(0, ω)`, which equals the initial voltage `V₀` when `X(0, ω) = 0`. -/
noncomputable def voltage (τ μ V₀ : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  μ + (V₀ - μ) * exp (-(t : ℝ) / τ) + X t ω

/-- The **firing time** (first-passage infimum): Mathlib's `hittingAfter` of the membrane voltage
`V(t)` to `[θ, ∞)` starting from `0`, taking values in `WithTop ℝ≥0` (`⊤` if the hit set
`{t ≥ 0 | θ ≤ V(t)}` is empty). For an arbitrary path this is the infimum of the hit set (not
necessarily attained at that time for discontinuous paths); for continuous paths it is the first
time `V(t) ≥ θ`. -/
noncomputable def firingTime (τ μ V₀ θ : ℝ) (X : ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (voltage τ μ V₀ X) (Set.Ici θ) 0

/-- The finite value of the firing time as a real number (`untopD 0`: `0` on the event that the
neuron never fires). -/
noncomputable def firingTimeValue (τ μ V₀ θ : ℝ) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  (WithTop.untopD (0 : ℝ≥0) (firingTime τ μ V₀ θ X ω) : ℝ≥0)

/-- **Siegert formula** (Siegert 1951). Let `P` be a probability measure, `τ > 0`, `σ > 0`,
`V₀ < θ`, and let `X` be an Ornstein–Uhlenbeck process started at `0` with rate `1/τ` and noise
amplitude `σ / √τ` under `P`, every path of which is continuous. Then the firing time of
`V(t) = μ + (V₀ - μ) e^{-t/τ} + X(t)` at threshold `θ` (with values in `WithTop ℝ≥0`) is finite
almost surely, its finite value `firingTimeValue` is integrable, and its mean is
`τ √π ∫_{(V₀-μ)/σ}^{(θ-μ)/σ} e^{u²} (1 + erf u) du`.

Sources: A. J. F. Siegert, "On the first passage time probability problem", Phys. Rev. 81
(1951) 617–623; "Mean time-to-fire for the noisy LIF neuron: a detailed derivation of the
Siegert formula", arXiv:1501.04032. -/
public theorem_wanted integral_firingTime (P : Measure Ω) [IsProbabilityMeasure P]
    (τ μ σ V₀ θ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hV₀ : V₀ < θ) (X : ℝ≥0 → Ω → ℝ)
    (hX : IsOrnsteinUhlenbeckFromZero (1 / τ) (σ / √τ) X P)
    (hcont : ∀ ω, Continuous fun t => X t ω) :
    (∀ᵐ ω ∂P, firingTime τ μ V₀ θ X ω ≠ ⊤) ∧
      Integrable (firingTimeValue τ μ V₀ θ X) P ∧
      ∫ ω, firingTimeValue τ μ V₀ θ X ω ∂P = siegertTime τ μ σ V₀ θ

end WantedExt.Biology.Neuroscience.SiegertFormulaWanted
