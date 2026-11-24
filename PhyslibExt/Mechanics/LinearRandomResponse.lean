/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.OrnsteinUhlenbeck
public import PhyslibExt.Units.EngineeringQuantities
import MathlibExt.Probability.BrownianMotionExistence
import MathlibExt.Probability.OrnsteinUhlenbeckSDE

/-!
# First-order random response through the stationary Ornstein–Uhlenbeck law

A first-order mechanical system with viscous damping coefficient `c > 0` and stiffness `k > 0`,
driven by a white-noise force, obeys `c dx = -k x dt + σ dW` for a standard Brownian motion `W`,
where `σ` is the coefficient of `dW`. Dividing by `c` gives the Langevin equation of the existing
scalar Ornstein–Uhlenbeck (OU) process with rate `θ = k / c` and noise amplitude `σ' = σ / c`.
This module makes that identification precise, reuses the existence and covariance of the
stationary OU law, and derives the stationary displacement variance `σ² / (2 c k)` together with
its dimension.

## i. Overview

* Dimensions (A). Over the seven-base ISQ, a damping coefficient (force per velocity) has the
  dimension `M T⁻¹` and the noise coefficient `σ` has `M L T^(-3/2)`, a force times the square
  root of a time, because the Brownian increment `dW` has the dimension `T^(1/2)`. Then `k / c`
  is a rate `T⁻¹`, `σ / c` has `L T^(-1/2)`, and `σ² / (c k)` is a displacement squared. The
  real-coordinate formula `σ² / (2 c k)` commutes with every change of positive unit scales,
  with output dimension `L²`; this instantiates `dimScale_mul` and `dimScale_inv`.
* Pathwise form (B). For a continuous driving path `w`, the integral form
  `c (x t - x₀) = -k ∫₀ᵗ x + σ (w t - w 0)` of the physical equation is, for `c > 0`, the integral
  form of the Langevin equation with `θ = k / c` and `σ' = σ / c`. Its unique continuous
  solution on `t ≥ 0` is the existing `ouPathSolution (k / c) (σ / c) x₀ w`.
* Stationary law (C). The stationary response is a stationary OU process with rate `k / c` and
  noise amplitude `σ / c`. For all `c, k > 0` and `σ` there is a probability space carrying a
  Brownian motion `B` and an independent start `X₀ ~ N(0, σ² / (2 c k))` on which the OU path
  solution driven by `B` solves the physical integral equation along almost every path and is
  such a stationary process. Its covariance is `σ² / (2 c k) · e^{-(k / c)|t - s|}`, its variance
  `σ² / (2 c k)` and its one-time law `N(0, σ² / (2 c k))`.
* Boundaries (D). The stationary variance vanishes exactly when `σ = 0`. The difference
  quotients `(W (t + h) - W t) / h` of a Brownian motion have variance `1 / h`, unbounded as
  `h → 0`; this is the reason the equation is read in integral form. No statement about
  convergence of the difference quotients, or about pathwise or mean-square derivatives, is
  made.

Model inputs (hypotheses):

* `W` is a standard Brownian motion and `σ` is the coefficient of `dW`, not a spectral density.
  The white-noise force `σ dW / dt` has autocorrelation `σ² δ(τ)`, so its constant spectral
  density `S₀` depends on the Fourier convention: `σ² = 2 π S₀` for the two-sided density in
  angular frequency `ω` normalized by `R(τ) = ∫ S(ω) e^{iωτ} dω` (Crandall and Mark 1963),
  `σ² = S₀` for the two-sided density in cyclic frequency `f` normalized by
  `R(τ) = ∫ S(f) e^{2πifτ} df`, and `σ² = G₀ / 2` for the one-sided cyclic density
  `G(f) = 2 S(f)` on `f ≥ 0`. No statement of this module uses a spectral density;
* `c > 0` and `k > 0`; the response is the stationary solution (stationary initialization);
* scalar values are coordinates in one coherent unit choice: `x` a displacement, `c` a damping
  coefficient, `k` a translational stiffness, `σ` a force times the square root of a time.

Non-goals: no second-order (mass-spring-damper) response, which needs a vector OU law; no
stochastic integral beyond the reused OU objects; no empirical adequacy or system safety claim.

## ii. Key results

- `dampingDim_exponent`, `forceNoiseDim_exponent` : the exponent vectors of the new dimension
  names.
- `stiffness_div_damping`, `forceNoise_div_damping`, `stationaryVarianceDim` : the rate, the OU
  noise amplitude and the stationary variance have the dimensions `T⁻¹`, `L T^(-1/2)` and `L²`.
- `stationaryVariance_coord_dimScale` : the variance formula commutes with a change of units.
- `physical_iff_langevin`, `ouPathSolution_solves_physical`, `eq_ouPathSolution_of_physical` :
  the physical equation is the Langevin equation with `θ = k / c` and `σ' = σ / c`.
- `exists_stationaryResponse` : a pathwise stationary response exists, driven by a Brownian
  motion with an independent stationary start.
- `stationaryResponse_covariance`, `stationaryResponse_variance`, `stationaryResponse_hasLaw` :
  covariance, variance and law of the stationary response.
- `stationaryResponse_variance_eq_zero_iff` : nonzero noise gives nonzero variance, and only
  nonzero noise does.
- `variance_brownian_diffQuot`, `not_bdd_variance_brownian_diffQuot` : the difference quotients
  of a Brownian motion have variance `1 / h`, which is unbounded as `h → 0`.

## iii. Table of contents

- A. Dimensions of the physical parameters
- B. Pathwise form of the physical equation
- C. The stationary response law
- D. Nonzero noise and the white-noise boundary

## iv. References

- G. E. Uhlenbeck and L. S. Ornstein, *On the theory of the Brownian motion*, Phys. Rev. 36
  (1930), 823–841.
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer
  (1991), Section 5.6.
- S. H. Crandall and W. D. Mark, *Random Vibration in Mechanical Systems*, Academic Press
  (1963), Chapter 2 (white-noise excitation of linear systems).
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Dimension Units.QuantityDimensions
  Units.EngineeringQuantities
open scoped NNReal

namespace Mechanics.LinearRandomResponse

/-! ## A. Dimensions of the physical parameters -/

/-- The dimension `M T⁻¹` of a viscous damping coefficient, a force per velocity. -/
def dampingDim : Dimension ISQDimensionBase :=
  forceDim / (single ISQDimensionBase.length / single ISQDimensionBase.time)

/-- The dimension `M L T^(-3/2)` of the coefficient `σ` of `dW` in `c dx = -k x dt + σ dW`: a
force times the square root of a time, since the Brownian increment has the dimension
`T^(1/2)`. -/
def forceNoiseDim : Dimension ISQDimensionBase :=
  forceDim * single ISQDimensionBase.time ^ (1 / 2 : Exponent)

/-- The exponents of `dampingDim` at the seven ISQ base quantities. -/
lemma dampingDim_exponent (b : ISQDimensionBase) :
    dampingDim.exponent b =
      match b with
      | .length => 0
      | .mass => 1
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `forceNoiseDim` at the seven ISQ base quantities. -/
lemma forceNoiseDim_exponent (b : ISQDimensionBase) :
    forceNoiseDim.exponent b =
      match b with
      | .length => 1
      | .mass => 1
      | .time => -3 / 2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The mean-reversion rate `θ = k / c` is a rate: a stiffness over a damping coefficient has
the dimension `T⁻¹`. -/
lemma stiffness_div_damping :
    translationalStiffnessDim / dampingDim = (single ISQDimensionBase.time)⁻¹ := by
  decide

/-- The OU noise amplitude `σ' = σ / c` has the dimension `L T^(-1/2)`, so `σ' dW` is a
displacement. -/
lemma forceNoise_div_damping :
    forceNoiseDim / dampingDim =
      single ISQDimensionBase.length * single ISQDimensionBase.time ^ (-1 / 2 : Exponent) := by
  decide

/-- The stationary variance `σ² / (2 c k)` has the dimension of a displacement squared. -/
lemma stationaryVarianceDim :
    forceNoiseDim * forceNoiseDim / (dampingDim * translationalStiffnessDim) =
      single ISQDimensionBase.length * single ISQDimensionBase.length := by
  decide

/-- The stationary-variance formula commutes with every change of unit scales: converting the
coordinates of `σ`, `c` and `k` and evaluating `σ² / (2 c k)` gives the converted coordinate of
the displacement variance. -/
lemma stationaryVariance_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (σ c k : ℝ)
    (_hc : 0 < c) (_hk : 0 < k) :
    ((u1.dimScale u2 forceNoiseDim : ℝ) * σ) ^ 2 /
        (2 * ((u1.dimScale u2 dampingDim : ℝ) * c) *
          ((u1.dimScale u2 translationalStiffnessDim : ℝ) * k)) =
      (u1.dimScale u2 (single ISQDimensionBase.length * single ISQDimensionBase.length) : ℝ) *
        (σ ^ 2 / (2 * c * k)) := by
  set sN : ℝ := (u1.dimScale u2 forceNoiseDim : ℝ) with hsN
  set sD : ℝ := (u1.dimScale u2 dampingDim : ℝ) with hsD
  set sK : ℝ := (u1.dimScale u2 translationalStiffnessDim : ℝ) with hsK
  set sL : ℝ := (u1.dimScale u2
    (single ISQDimensionBase.length * single ISQDimensionBase.length) : ℝ) with hsL
  have hD : sD ≠ 0 := (NNReal.coe_pos.mpr (dimScale_pos u1 u2 _)).ne'
  have hK : sK ≠ 0 := (NNReal.coe_pos.mpr (dimScale_pos u1 u2 _)).ne'
  have hdim : forceNoiseDim * forceNoiseDim =
      single ISQDimensionBase.length * single ISQDimensionBase.length *
        (dampingDim * translationalStiffnessDim) := by
    decide
  have h : sN * sN = sL * (sD * sK) := by
    rw [hsN, hsL, hsD, hsK, ← dimScale_mul, ← dimScale_mul, ← dimScale_mul, hdim]
  rw [show (sN * σ) ^ 2 = sN * sN * σ ^ 2 by ring, h,
    show 2 * (sD * c) * (sK * k) = (sD * sK) * (2 * c * k) by ring,
    show sL * (sD * sK) * σ ^ 2 = (sD * sK) * (sL * σ ^ 2) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hD hK)]
  ring

/-! ## B. Pathwise form of the physical equation -/

/-- **Physical and Langevin forms agree.** For `c > 0`, the integral form
`c (x t - x₀) = -k ∫₀ᵗ x + σ (w t - w 0)` of `c dx = -k x dt + σ dw` is the integral form
`x t = x₀ - θ ∫₀ᵗ x + σ' (w t - w 0)` of the Langevin equation with `θ = k / c` and
`σ' = σ / c`. -/
lemma physical_iff_langevin {c : ℝ} (hc : 0 < c) (k σ x₀ : ℝ) (x w : ℝ → ℝ) (t : ℝ) :
    c * (x t - x₀) = -k * (∫ u in (0 : ℝ)..t, x u) + σ * (w t - w 0) ↔
      x t = x₀ - k / c * (∫ u in (0 : ℝ)..t, x u) + σ / c * (w t - w 0) := by
  have hc0 : c ≠ 0 := hc.ne'
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- The existing OU path solution with `θ = k / c` and `σ' = σ / c` solves the physical equation
`c (x t - x₀) = -k ∫₀ᵗ x + σ (w t - w 0)` for every continuous driving path `w` and every
`t`. -/
lemma ouPathSolution_solves_physical {c : ℝ} (hc : 0 < c) (k σ x₀ : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (t : ℝ) :
    c * (ouPathSolution (k / c) (σ / c) x₀ w t - x₀) =
      -k * (∫ u in (0 : ℝ)..t, ouPathSolution (k / c) (σ / c) x₀ w u) + σ * (w t - w 0) := by
  exact (physical_iff_langevin hc k σ x₀ _ w t).2
    (ouPathSolution_integral_eq (k / c) (σ / c) x₀ hw t)

/-- **Uniqueness.** A continuous solution of the physical equation on `t ≥ 0` is the OU path
solution with `θ = k / c` and `σ' = σ / c` there. -/
lemma eq_ouPathSolution_of_physical {c k σ x₀ : ℝ} (hc : 0 < c) {w x : ℝ → ℝ}
    (hw : Continuous w) (hx : Continuous x)
    (h : ∀ t, 0 ≤ t → c * (x t - x₀) = -k * (∫ u in (0 : ℝ)..t, x u) + σ * (w t - w 0))
    {t : ℝ} (ht : 0 ≤ t) : x t = ouPathSolution (k / c) (σ / c) x₀ w t := by
  exact eq_ouPathSolution_of_integral_eq hw hx
    (fun t ht => (physical_iff_langevin hc k σ x₀ x w t).1 (h t ht)) ht

/-! ## C. The stationary response law -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Existence of a pathwise stationary response.** For `c, k > 0` and every `σ` there is a
probability space carrying a Brownian motion `B` and a start `X₀ ~ N(0, σ² / (2 c k))` independent
of `B` such that the OU path solution `X t ω = ouPathSolution (k / c) (σ / c) (X₀ ω) (B · ω) t`
solves the physical equation `c (x t - x₀) = -k ∫₀ᵗ x + σ (w t - w 0)` with `w = B · ω` along
almost every path, and is a stationary OU process with rate `k / c` and noise amplitude
`σ / c`. -/
lemma exists_stationaryResponse {c k : ℝ} (hc : 0 < c) (hk : 0 < k) (σ : ℝ) :
    ∃ μ : Measure (ℝ≥0 → ℝ), ∃ B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, ∃ X₀ : (ℝ≥0 → ℝ) → ℝ,
      IsBrownianReal B μ ∧ HasLaw X₀ (gaussianReal 0 (σ ^ 2 / (2 * c * k)).toNNReal) μ ∧
      IndepFun X₀ (fun ω t ↦ B t ω) μ ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ,
        c * (ouPathSolution (k / c) (σ / c) (X₀ ω) (fun u ↦ B u.toNNReal ω) t - X₀ ω) =
          -k * (∫ u in (0 : ℝ)..t,
            ouPathSolution (k / c) (σ / c) (X₀ ω) (fun u ↦ B u.toNNReal ω) u) +
            σ * (B t.toNNReal ω - B 0 ω)) ∧
      IsStationaryOrnsteinUhlenbeck (k / c) (σ / c)
        (fun t ω ↦ ouPathSolution (k / c) (σ / c) (X₀ ω) (fun u ↦ B u.toNNReal ω) t) μ := by
  obtain ⟨μ, B, X₀, hB, hX₀, hind⟩ :=
    exists_isBrownianReal_indepFun_gaussianReal (σ ^ 2 / (2 * c * k)).toNNReal
  have hc0 : c ≠ 0 := hc.ne'
  have hk0 : k ≠ 0 := hk.ne'
  have hv : (σ / c) ^ 2 / (2 * (k / c)) = σ ^ 2 / (2 * c * k) := by field_simp
  refine ⟨μ, B, X₀, hB, hX₀, hind, ?_, ?_⟩
  · filter_upwards [hB.cont] with ω hω t
    have hw : Continuous fun u : ℝ ↦ B u.toNNReal ω := hω.comp continuous_real_toNNReal
    have h := ouPathSolution_solves_physical hc k σ (X₀ ω) hw t
    rwa [Real.toNNReal_zero] at h
  · exact IsBrownianReal.isStationaryOrnsteinUhlenbeck_ouPathSolution hB (div_pos hk hc)
      (σ / c) (by rwa [hv]) hind

/-- **Covariance of the stationary response**:
`cov(X s, X t) = σ² / (2 c k) · e^{-(k / c)|t - s|}`. -/
lemma stationaryResponse_covariance {c k σ : ℝ} (hc : 0 < c) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck (k / c) (σ / c) X P) (s t : ℝ≥0) :
    cov[X s, X t; P] = σ ^ 2 / (2 * c * k) * Real.exp (-(k / c) * |(t : ℝ) - s|) := by
  have hk : 0 < k := by
    have h := hX.rate_pos
    rwa [div_pos_iff_of_pos_right hc] at h
  rw [hX.covariance_eval, ouStationaryCovariance]
  congr 1
  field_simp

/-- **Stationary variance** of the displacement: `Var (X t) = σ² / (2 c k)`. -/
lemma stationaryResponse_variance {c k σ : ℝ} (hc : 0 < c) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck (k / c) (σ / c) X P) (t : ℝ≥0) :
    Var[X t; P] = σ ^ 2 / (2 * c * k) := by
  have hk : 0 < k := by
    have h := hX.rate_pos
    rwa [div_pos_iff_of_pos_right hc] at h
  rw [← covariance_self (hX.isGaussianProcess.aemeasurable t), hX.covariance_eval,
    ouStationaryCovariance_self]
  field_simp

/-- **Stationary law** of the displacement: `X t ~ N(0, σ² / (2 c k))`. -/
lemma stationaryResponse_hasLaw {c k σ : ℝ} (hc : 0 < c) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck (k / c) (σ / c) X P) (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 (σ ^ 2 / (2 * c * k)).toNNReal) P := by
  have hk : 0 < k := by
    have h := hX.rate_pos
    rwa [div_pos_iff_of_pos_right hc] at h
  have h := hX.hasLaw_eval t
  rwa [show (σ / c) ^ 2 / (2 * (k / c)) = σ ^ 2 / (2 * c * k) by field_simp] at h

/-! ## D. Nonzero noise and the white-noise boundary -/

/-- **Nonzero noise gives nonzero variance**, and only nonzero noise does: the stationary
variance vanishes exactly when `σ = 0`. -/
lemma stationaryResponse_variance_eq_zero_iff {c k σ : ℝ} (hc : 0 < c) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck (k / c) (σ / c) X P) (t : ℝ≥0) :
    Var[X t; P] = 0 ↔ σ = 0 := by
  have hk : 0 < k := by
    have h := hX.rate_pos
    rwa [div_pos_iff_of_pos_right hc] at h
  rw [stationaryResponse_variance hc hX t]
  simp [hc.ne', hk.ne']

/-- **Variance of a Brownian difference quotient.** The difference quotient
`(W (t + h) - W t) / h` of a pre-Brownian motion has variance `1 / h` for every `h > 0`. -/
lemma variance_brownian_diffQuot {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t h : ℝ≥0)
    (hh : 0 < h) :
    Var[fun ω => (B (t + h) ω - B t ω) / (h : ℝ); P] = 1 / (h : ℝ) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hvar : Var[B (t + h) - B t; P] = h := by
    rw [(hB.hasLaw_sub (t + h) t).variance_eq]
    simp [variance_id_gaussianReal]
  have heq : (fun ω => (B (t + h) ω - B t ω) / (h : ℝ)) =
      fun ω => (h : ℝ)⁻¹ * (B (t + h) - B t) ω := by
    funext ω
    simp [div_eq_inv_mul]
  rw [heq, variance_const_mul, hvar]
  field_simp

/-- **Unbounded difference-quotient variance.** No bound holds for the variances of the
difference quotients `(W (t + h) - W t) / h` of a pre-Brownian motion over `h > 0`; they grow
like `1 / h` as `h → 0`. This is the formal content behind reading the physical equation in the
integral form of section B. -/
lemma not_bdd_variance_brownian_diffQuot {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) :
    ¬ ∃ C : ℝ, ∀ h : ℝ≥0, 0 < h → Var[fun ω => (B (t + h) ω - B t ω) / (h : ℝ); P] ≤ C := by
  rintro ⟨C, hC⟩
  have hε : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  have hpos : (0 : ℝ≥0) < (1 / (|C| + 1)).toNNReal := Real.toNNReal_pos.mpr hε
  have h1 := hC _ hpos
  rw [variance_brownian_diffQuot hB t _ hpos, Real.coe_toNNReal _ hε.le, one_div_one_div] at h1
  have := le_abs_self C
  linarith

end Mechanics.LinearRandomResponse
