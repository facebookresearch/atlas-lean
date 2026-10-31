/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Tests for the Ornstein–Uhlenbeck process

Non-vacuity witnesses for `IsOrnsteinUhlenbeckFromZero` and `IsStationaryOrnsteinUhlenbeck`, the
degenerate case `σ = 0`, boundary values of the covariance functions (time `0`, the junk value at
`θ = 0`), concrete variances, the relaxation of the variance to the stationary value, a concrete
transition law, and the pathwise solution without noise.
-/

@[expose] public section

open MeasureTheory Filter Topology Real ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MathlibExtTest.Probability.OrnsteinUhlenbeck

/-! ### Non-vacuity -/

/-- An Ornstein–Uhlenbeck process started at `0` exists (`θ = 1`, `σ = 1`). -/
example : ∃ μ : Measure (ℝ≥0 → ℝ), ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, IsOrnsteinUhlenbeckFromZero 1 1 X μ :=
  exists_isOrnsteinUhlenbeckFromZero one_pos 1

/-- A stationary Ornstein–Uhlenbeck process exists (`θ = 1/2`, `σ = 3`). -/
example : ∃ μ : Measure (ℝ≥0 → ℝ), ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
    IsStationaryOrnsteinUhlenbeck (1 / 2) 3 X μ :=
  exists_isStationaryOrnsteinUhlenbeck (by norm_num) 3

/-- Degenerate noise `σ = 0`: the zero process on a one-point space is an OU process. -/
example : IsOrnsteinUhlenbeckFromZero 1 0 (fun _ _ ↦ (0 : ℝ)) (Measure.dirac ()) where
  rate_pos := one_pos
  isGaussianProcess := ⟨fun I ↦ ⟨measurable_const.aemeasurable,
    by rw [Measure.map_const]; simp; infer_instance⟩⟩
  integral_eval _ := by simp
  covariance_eval _ _ := by simp [ouCovariance]

/-! ### Covariance functions -/

/-- The process started at `0` has zero covariance with its value at time `0`. -/
example (θ σ : ℝ) (t : ℝ≥0) : ouCovariance θ σ 0 t = 0 := by
  simp [ouCovariance]

/-- Junk value outside the domain: at `θ = 0` the division by zero makes the covariance `0`,
which is why `0 < θ` is a field of `IsOrnsteinUhlenbeckFromZero`. -/
example (σ s t : ℝ) : ouCovariance 0 σ s t = 0 := by
  simp [ouCovariance]

/-- `θ = 1/2`, `σ = 1`: the variance at time `t` is `1 - e^{-t}`. -/
example (t : ℝ) : ouCovariance (1 / 2) 1 t t = 1 - exp (-t) := by
  rw [ouCovariance_self]
  norm_num

/-- `θ = 1`, `σ = 2`: the stationary variance is `2`. -/
example (t : ℝ) : ouStationaryCovariance 1 2 t t = 2 := by
  rw [ouStationaryCovariance_self]
  norm_num

/-- The stationary covariance at lag `1` with `θ = 1`, `σ = √2` is `e^{-1}`. -/
example : ouStationaryCovariance 1 (√2) 0 1 = exp (-1) := by
  simp [ouStationaryCovariance]

/-- The variance of the process started at `0` relaxes to the stationary variance. -/
example {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    Tendsto (fun h : ℝ ↦ ouCovariance θ σ h h) atTop (𝓝 (σ ^ 2 / (2 * θ))) := by
  simpa [ouStationaryCovariance] using tendsto_ouCovariance_add hθ σ 0 0

/-! ### Laws -/

/-- The stationary law with `θ = 1`, `σ = √2` is the standard normal law. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck 1 (√2) X P) (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 1) P := by
  have h := hX.hasLaw_eval t
  have h1 : (√2 ^ 2 / (2 * 1) : ℝ).toNNReal = 1 := by simp
  rwa [h1] at h

/-- A concrete transition law: for the stationary process with `θ = 1`, `σ = √2`, given
`X 0 = x` the law of `X 1` is `N(e^{-1} x, 1 - e^{-2})`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStationaryOrnsteinUhlenbeck 1 (√2) X P)
    (hm : ∀ t, Measurable (X t)) :
    ∀ᵐ x ∂(P.map (X 0)), condDistrib (X 1) (X 0) P x =
      gaussianReal (exp (-1) * x) (1 - exp (-2)).toNNReal := by
  filter_upwards [hX.condDistrib_eval hm (zero_le : (0 : ℝ≥0) ≤ 1)] with x hx
  rw [hx]
  norm_num

/-! ### Pathwise Langevin equation -/

/-- Without noise the pathwise solution is the deterministic relaxation `e^{-θt} x₀`. -/
example (θ x₀ t : ℝ) (w : ℝ → ℝ) : ouPathSolution θ 0 x₀ w t = exp (-θ * t) * x₀ := by
  simp [ouPathSolution]

/-- The pathwise solution started at `x₀ = 1` with `θ = 1`, `σ = 0` satisfies the integral
equation at time `1`. -/
example : ouPathSolution 1 0 1 (fun _ ↦ 0) 1 =
    1 - 1 * (∫ u in (0 : ℝ)..1, ouPathSolution 1 0 1 (fun _ ↦ 0) u) + 0 * (0 - 0) :=
  ouPathSolution_integral_eq 1 0 1 continuous_const 1

end MathlibExtTest.Probability.OrnsteinUhlenbeck
