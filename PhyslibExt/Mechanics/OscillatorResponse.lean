/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Solution
public import PhyslibExt.Units.EngineeringQuantities
import MathlibExt.Analysis.ODE.Duhamel

/-!
# Damping and forcing parameter correspondence, forced response and resonance

An engineering mass-spring-damper has mass `m > 0`, viscous damping coefficient `c ≥ 0`
(force per velocity) and stiffness `k > 0` (force per length):

  `m x'' + c x' + k x = F cos (Ω t)`,

with initial position `x₀`, initial velocity `v₀` and a forcing amplitude `F` in force units.
This module maps these parameters to Physlib's damped harmonic oscillator and to the
forced-oscillator convention `x'' + 2 γ x' + ω₀ ^ 2 x = F cos (Ω t)`, constructs the forced
response with its uniqueness, and treats the undamped exact resonance as a separate branch.

## i. Overview

Physlib's damped oscillator takes the damping coefficient `γ = c` itself
(`massSpringDamper`); its equation of motion is the free equation above, its regime is read
off `c ^ 2 - 4 m k`, and its selected free trajectory is the unique smooth solution with the
given initial position and velocity. The forced-oscillator convention uses `γ = c / (2 m)`,
`ω₀ = √(k / m)` and the forcing amplitude `F / m`, which is an acceleration, not a force. The
two damping conventions differ by the factor `2 m`, and `k = 0` is not a Physlib oscillator.
Physlib's uniqueness statement is for smooth (`ContDiff ℝ ∞`) trajectories.

For the force `F cos (Ω t)` let `D = (k - m Ω ^ 2) ^ 2 + (c Ω) ^ 2` be the steady-state
denominator; it vanishes exactly at the undamped exact resonance `c = 0`, `k = m Ω ^ 2`, which
is excluded. The particular response `x_p (t) = A cos (Ω t) + B sin (Ω t)` with
`A = F (k - m Ω ^ 2) / D` and `B = F c Ω / D` is differentiated explicitly and solves the forced
equation; its coefficients are those of the forced-oscillator convention. The forced response
adds the free trajectory whose initial position and velocity are both corrected by the
particular response, `x₀ - x_p (0)` and `v₀ - x_p' (0)`. On the phase space `(x, x')` the forced
equation reads `z' = L z + b (t)` with `L (x, v) = (v, -(k x + c v) / m)` and
`b (t) = (0, F cos (Ω t) / m)`, so twice continuously differentiable displacements correspond
to phase-space solutions, and Duhamel's variation-of-constants theorem gives uniqueness of the
forced response among them, a larger class than the smooth one above.

At the excluded undamped exact resonance, `c = 0` and forcing at the natural angular frequency
`ω₀` with `k = m ω₀ ^ 2`, the steady-state formula has no meaning. There the secular response
`x (t) = F t sin (ω₀ t) / (2 m ω₀)` is differentiated explicitly and solves
`m x'' + k x = F cos (ω₀ t)` from rest at the origin. For `m, ω₀ > 0` its envelope is
`|F| |t| / (2 m ω₀)`, and its absolute value meets the envelope at the times
`t_n = (2 π n + π / 2) / ω₀`, where `sin (ω₀ t_n) = 1`. For `F ≠ 0` these times are not extrema of
the response, whose velocity there is `F / (2 m ω₀) ≠ 0`, and along them the amplitude grows
without bound. With any nonzero damping the same function is not a solution.

Parameters, forcing and initial data are model inputs.

## ii. Key results

- `massSpringDamper_params`: Physlib parameters, decay rate `c / (2 m)`, natural frequency
  `√(k / m)`, and `γ = 2 m (c / (2 m))`.
- `equationOfMotion_iff`: the free equation of motion is `m x'' + c x' + k x = 0`.
- `forced_equation_iff`: the forced equation with force amplitude `F` is the convention's
  equation with damping `c / (2 m)`, frequency `√(k / m)` and forcing `F / m`.
- `regime_iff`: the damping regimes by `c ^ 2` against `4 m k` and by the convention's damping
  rate against its natural frequency.
- `trajectory_initial_data`: the selected free trajectory solves the equation, has the
  engineering initial data, and is the only smooth solution that does.
- `energy_dissipation`: the mechanical energy decreases at the rate `c ‖x'‖ ^ 2`.
- `atlasForcing_dimension`: the forcing amplitude `F / m` has dimension `L T⁻²`, not that of a
  force.
- `steadyStateDenominator_ne_zero_iff`: the steady-state denominator is nonzero exactly off the
  undamped exact resonance.
- `steadyState_coefficients_convention`: the steady-state coefficients are those of the
  forced-oscillator convention.
- `hasDerivAt_particularResponse`, `hasDerivAt_particularVelocity`, `particularResponse_solves`:
  the derivatives of the particular response and the forced equation it solves.
- `forcedResponse_spec`: the forced response is twice continuously differentiable, solves the
  forced equation and has initial position `x₀` and velocity `v₀`.
- `phase_of_displacement`, `displacement_of_phase`: twice continuously differentiable solutions
  of the forced equation correspond to solutions of the phase-space equation.
- `forcedResponse_unique`: the forced response is the only twice continuously differentiable
  solution with its initial data.
- `resonance_branch_params`, `steadyStateDenominator_eq_zero_iff`: the resonance branch is forcing
  at the natural frequency without damping, exactly where the steady-state denominator vanishes.
- `hasDerivAt_resonantResponse`, `hasDerivAt_resonantVelocity`, `resonantResponse_solves`,
  `resonantResponse_initial`: the derivatives of the secular response, which solves the undamped
  resonant equation from rest at the origin.
- `abs_resonantResponse_le`, `resonantResponse_resonanceEnvelopeTime`,
  `abs_resonantResponse_resonanceEnvelopeTime`: the envelope, the signed values at the
  envelope-touch times, and the envelope attained there by the absolute value.
- `tendsto_resonanceEnvelopeTime`, `tendsto_abs_resonantResponse_resonanceEnvelopeTime`: the
  envelope-touch times and the amplitude along them tend to infinity.
- `resonantResponse_not_solves_damped`: with nonzero damping the secular response is not a
  solution.

## iii. Table of contents

- A. Model
- B. Parameter map
- C. Regimes, free trajectories and dissipation
- D. Force units
- E. Forced-response model
- F. Steady-state denominator and coefficients
- G. The particular response
- H. The forced response
- I. Phase space and uniqueness
- J. Undamped resonance model
- K. The resonance branch
- L. Resonant derivatives and equation of motion
- M. Unbounded amplitude
- N. Damping leaves the branch

## iv. References

- S. S. Rao, *Mechanical Vibrations*, 6th edition, chapters 2-3 (viscously damped free and
  harmonically forced single-degree-of-freedom systems).
- L. D. Landau and E. M. Lifshitz, *Mechanics*, §25 (damped oscillations).
- D. J. Inman, *Engineering Vibration*, 4th edition, Section 2.1 (harmonic excitation of undamped
  systems and resonance).
- `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` and `.Solution`: the carrier,
  equation of motion, regimes, energy dissipation and selected trajectory reused here.
- `PhyslibExt.EarthScience.DampedOscillator`: the forced-oscillator convention
  `x'' + 2 γ x' + ω₀ ^ 2 x = F cos (ω t)`.
- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS (2012), Sections 1.1
  and 3.2 (reduction to a first-order system, variation of constants).
- `MathlibExt.Analysis.ODE.Duhamel`: Duhamel's variation-of-constants theorem, used for the
  uniqueness of the forced response.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.OscillatorResponse

open ClassicalMechanics Time ContDiff

/-! ## A. Model -/

/-- The Physlib damped oscillator of an engineering mass-spring-damper with mass `m > 0`,
viscous damping coefficient `c ≥ 0` and stiffness `k > 0`. Physlib's damping coefficient is
`c` itself. -/
def massSpringDamper (m c k : ℝ) (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) :
    DampedHarmonicOscillator where
  m := m
  k := k
  m_pos := hm
  k_pos := hk
  γ := c
  γ_nonneg := hc

/-- Damping rate `c / (2 m)` of the forced-oscillator convention
`x'' + 2 γ x' + ω₀ ^ 2 x = F cos (Ω t)`. -/
noncomputable def atlasDamping (m c : ℝ) : ℝ :=
  c / (2 * m)

/-- Natural angular frequency `√(k / m)` of that convention. -/
noncomputable def atlasNaturalFrequency (m k : ℝ) : ℝ :=
  Real.sqrt (k / m)

/-- Forcing amplitude of that convention: the force amplitude `F` per unit mass. -/
noncomputable def atlasForcing (m F : ℝ) : ℝ :=
  F / m

/-- Engineering initial position and velocity as Physlib initial conditions on the
one-dimensional coordinate line. -/
noncomputable def initialConditions (x₀ v₀ : ℝ) : DampedHarmonicOscillator.InitialConditions where
  x₀ := EuclideanSpace.single 0 x₀
  v₀ := EuclideanSpace.single 0 v₀

/-! ## B. Parameter map -/

/-- The Physlib parameters are the engineering ones, with damping `γ = c`; its decay rate is
the convention's `c / (2 m)`, its natural frequency is `√(k / m)`, and the two damping
coefficients differ by the factor `2 m`. -/
lemma massSpringDamper_params {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) :
    (massSpringDamper m c k hm hc hk).m = m ∧ (massSpringDamper m c k hm hc hk).k = k ∧
      (massSpringDamper m c k hm hc hk).γ = c ∧
      (massSpringDamper m c k hm hc hk).decayRate = atlasDamping m c ∧
      (massSpringDamper m c k hm hc hk).ω = atlasNaturalFrequency m k ∧
      (massSpringDamper m c k hm hc hk).γ = 2 * m * atlasDamping m c := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  change c = 2 * m * (c / (2 * m))
  field_simp

/-- The Physlib free equation of motion of the mass-spring-damper is
`m x'' + c x' + k x = 0`. -/
lemma equationOfMotion_iff {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k)
    (x : Time → EuclideanSpace ℝ (Fin 1)) :
    (massSpringDamper m c k hm hc hk).EquationOfMotion x ↔
      ∀ t : Time, m • ∂ₜ (∂ₜ x) t + c • ∂ₜ x t + k • x t = 0 := by
  exact Iff.rfl

/-- The forced equation with physical force amplitude `F` is the forced-oscillator convention
with damping `c / (2 m)`, natural frequency `√(k / m)` and forcing amplitude `F / m`. -/
lemma forced_equation_iff {m c k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (F Ω : ℝ) (x : ℝ → ℝ) :
    (∀ t, m * deriv (deriv x) t + c * deriv x t + k * x t = F * Real.cos (Ω * t)) ↔
      ∀ t, deriv (deriv x) t + 2 * atlasDamping m c * deriv x t +
          atlasNaturalFrequency m k ^ 2 * x t = atlasForcing m F * Real.cos (Ω * t) := by
  have hω : atlasNaturalFrequency m k ^ 2 = k / m := Real.sq_sqrt (div_nonneg hk hm.le)
  have hm0 : m ≠ 0 := hm.ne'
  simp only [atlasDamping, atlasForcing, hω]
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-! ## C. Regimes, free trajectories and dissipation -/

/-- Regime classification: Physlib's discriminant regimes are `c ^ 2` against `4 m k`, and
equivalently the convention's damping rate against its natural frequency. -/
lemma regime_iff {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) :
    ((massSpringDamper m c k hm hc hk).IsUnderdamped ↔ c ^ 2 < 4 * m * k) ∧
      ((massSpringDamper m c k hm hc hk).IsUnderdamped ↔
        atlasDamping m c < atlasNaturalFrequency m k) ∧
      ((massSpringDamper m c k hm hc hk).IsCriticallyDamped ↔ c ^ 2 = 4 * m * k) ∧
      ((massSpringDamper m c k hm hc hk).IsCriticallyDamped ↔
        atlasDamping m c = atlasNaturalFrequency m k) ∧
      ((massSpringDamper m c k hm hc hk).IsOverdamped ↔ 4 * m * k < c ^ 2) ∧
      ((massSpringDamper m c k hm hc hk).IsOverdamped ↔
        atlasNaturalFrequency m k < atlasDamping m c) := by
  set S := massSpringDamper m c k hm hc hk
  have hdisc : S.discriminant = c ^ 2 - 4 * m * k := rfl
  refine ⟨?_, S.isUnderdamped_iff_decayRate_lt, ?_, ?_, ?_, S.isOverdamped_iff_lt_decayRate⟩
  · change S.discriminant < 0 ↔ _
    rw [hdisc]
    constructor <;> intro h <;> linarith
  · change S.discriminant = 0 ↔ _
    rw [hdisc]
    constructor <;> intro h <;> linarith
  · rw [S.isCriticallyDamped_iff_eq_decayRate]
    exact eq_comm
  · change 0 < S.discriminant ↔ _
    rw [hdisc]
    constructor <;> intro h <;> linarith

/-- The selected Physlib free trajectory for engineering initial data `x₀`, `v₀` solves the
equation of motion, starts at `x₀` with velocity `v₀`, and is the only smooth solution that
does. -/
lemma trajectory_initial_data {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) (x₀ v₀ : ℝ) :
    (massSpringDamper m c k hm hc hk).EquationOfMotion
        ((massSpringDamper m c k hm hc hk).trajectory (initialConditions x₀ v₀)) ∧
      (massSpringDamper m c k hm hc hk).trajectory (initialConditions x₀ v₀) 0 =
        EuclideanSpace.single 0 x₀ ∧
      ∂ₜ ((massSpringDamper m c k hm hc hk).trajectory (initialConditions x₀ v₀)) 0 =
        EuclideanSpace.single 0 v₀ ∧
      ∀ x : Time → EuclideanSpace ℝ (Fin 1), ContDiff ℝ ∞ x →
        (massSpringDamper m c k hm hc hk).EquationOfMotion x →
        x 0 = EuclideanSpace.single 0 x₀ → ∂ₜ x 0 = EuclideanSpace.single 0 v₀ →
        x = (massSpringDamper m c k hm hc hk).trajectory (initialConditions x₀ v₀) := by
  set S := massSpringDamper m c k hm hc hk
  exact ⟨S.trajectory_equationOfMotion _, S.trajectory_apply_zero _,
    S.trajectory_velocity_at_zero _,
    fun x hx hE h0 hv0 => S.trajectories_unique _ x hx hE h0 hv0⟩

/-- Along a smooth free solution the mechanical energy decreases at the rate `c ‖x'‖ ^ 2`. -/
lemma energy_dissipation {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k)
    (x : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ x)
    (hEOM : (massSpringDamper m c k hm hc hk).EquationOfMotion x) (t : Time) :
    ∂ₜ ((massSpringDamper m c k hm hc hk).energy x) t = -c * inner ℝ (∂ₜ x t) (∂ₜ x t) := by
  exact (massSpringDamper m c k hm hc hk).energy_dissipation_rate x t hEOM hx

/-! ## D. Force units -/

/-- The convention's forcing amplitude `F / m` has the dimension of an acceleration,
`L T⁻²`, not that of a force. -/
lemma atlasForcing_dimension :
    Units.EngineeringQuantities.forceDim / Dimension.single ISQDimensionBase.mass =
        Dimension.single ISQDimensionBase.length / Dimension.single ISQDimensionBase.time ^ 2 ∧
      Units.EngineeringQuantities.forceDim / Dimension.single ISQDimensionBase.mass ≠
        Units.EngineeringQuantities.forceDim := by
  exact ⟨by decide, by decide⟩

/-! ## E. Forced-response model -/

/-- The steady-state denominator `(k - m Ω ^ 2) ^ 2 + (c Ω) ^ 2` of the harmonic response to the
force `F cos (Ω t)`. -/
def steadyStateDenominator (m c k Ω : ℝ) : ℝ :=
  (k - m * Ω ^ 2) ^ 2 + (c * Ω) ^ 2

/-- The in-phase coefficient `A = F (k - m Ω ^ 2) / D` of the steady-state response. -/
noncomputable def steadyStateCos (m c k F Ω : ℝ) : ℝ :=
  F * (k - m * Ω ^ 2) / steadyStateDenominator m c k Ω

/-- The quadrature coefficient `B = F c Ω / D` of the steady-state response. -/
noncomputable def steadyStateSin (m c k F Ω : ℝ) : ℝ :=
  F * (c * Ω) / steadyStateDenominator m c k Ω

/-- The particular (steady-state) response `A cos (Ω t) + B sin (Ω t)`. -/
noncomputable def particularResponse (m c k F Ω t : ℝ) : ℝ :=
  steadyStateCos m c k F Ω * Real.cos (Ω * t) + steadyStateSin m c k F Ω * Real.sin (Ω * t)

/-- The velocity `Ω (B cos (Ω t) - A sin (Ω t))` of the particular response. -/
noncomputable def particularVelocity (m c k F Ω t : ℝ) : ℝ :=
  Ω * (steadyStateSin m c k F Ω * Real.cos (Ω * t) -
    steadyStateCos m c k F Ω * Real.sin (Ω * t))

/-- The forced response with initial position `x₀` and velocity `v₀`: the particular response
plus the Physlib free trajectory whose initial position and velocity are both corrected by the
particular response, read on the real time line. -/
noncomputable def forcedResponse (m c k : ℝ) (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k)
    (F Ω x₀ v₀ t : ℝ) : ℝ :=
  particularResponse m c k F Ω t +
    (massSpringDamper m c k hm hc hk).trajectory
      (initialConditions (x₀ - particularResponse m c k F Ω 0)
        (v₀ - particularVelocity m c k F Ω 0)) ⟨t⟩ 0

/-- The phase-space operator `(x, v) ↦ (v, -(k x + c v) / m)` of the mass-spring-damper. -/
noncomputable def phaseOperator (m c k : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-(k / m)) • ContinuousLinearMap.fst ℝ ℝ ℝ + (-(c / m)) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The phase-space forcing `t ↦ (0, F cos (Ω t) / m)`. -/
noncomputable def phaseForcing (m F Ω t : ℝ) : ℝ × ℝ :=
  (0, F * Real.cos (Ω * t) / m)

/-! ## F. Steady-state denominator and coefficients -/

/-- For `k > 0` the steady-state denominator is nonzero exactly off the undamped exact
resonance `c = 0`, `k = m Ω ^ 2`. -/
lemma steadyStateDenominator_ne_zero_iff {m c k : ℝ} (hk : 0 < k) (Ω : ℝ) :
    steadyStateDenominator m c k Ω ≠ 0 ↔ ¬ (c = 0 ∧ k = m * Ω ^ 2) := by
  unfold steadyStateDenominator
  constructor
  · rintro hD ⟨rfl, hkΩ⟩
    apply hD
    rw [hkΩ]
    ring
  · intro h hD
    apply h
    have h1 : (k - m * Ω ^ 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (k - m * Ω ^ 2), sq_nonneg (c * Ω)]
    have h2 : (c * Ω) ^ 2 = 0 := by
      nlinarith [sq_nonneg (k - m * Ω ^ 2), sq_nonneg (c * Ω)]
    have hkΩ : k = m * Ω ^ 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    have hΩ : Ω ≠ 0 := by
      rintro rfl
      simp at hkΩ
      linarith
    have hcΩ : c * Ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    exact ⟨(mul_eq_zero.mp hcΩ).resolve_right hΩ, hkΩ⟩

/-- The coefficients are those of the forced-oscillator convention
`x'' + 2 γ x' + ω₀ ^ 2 x = f cos (Ω t)` with `γ = c / (2 m)`, `ω₀ = √(k / m)`, `f = F / m`:
`A = f (ω₀ ^ 2 - Ω ^ 2) / D'` and `B = f (2 γ Ω) / D'`, with
`D' = (ω₀ ^ 2 - Ω ^ 2) ^ 2 + (2 γ Ω) ^ 2`. -/
lemma steadyState_coefficients_convention {m c k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (F Ω : ℝ) :
    steadyStateCos m c k F Ω =
        atlasForcing m F * (atlasNaturalFrequency m k ^ 2 - Ω ^ 2) /
          ((atlasNaturalFrequency m k ^ 2 - Ω ^ 2) ^ 2 + (2 * atlasDamping m c * Ω) ^ 2) ∧
      steadyStateSin m c k F Ω =
        atlasForcing m F * (2 * atlasDamping m c * Ω) /
          ((atlasNaturalFrequency m k ^ 2 - Ω ^ 2) ^ 2 + (2 * atlasDamping m c * Ω) ^ 2) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hω : atlasNaturalFrequency m k ^ 2 = k / m := Real.sq_sqrt (div_nonneg hk hm.le)
  simp only [steadyStateCos, steadyStateSin, steadyStateDenominator, atlasForcing, atlasDamping, hω]
  have hden : (k / m - Ω ^ 2) ^ 2 + (2 * (c / (2 * m)) * Ω) ^ 2 =
      ((k - m * Ω ^ 2) ^ 2 + (c * Ω) ^ 2) / m ^ 2 := by
    field_simp
  have hnumA : F / m * (k / m - Ω ^ 2) = F * (k - m * Ω ^ 2) / m ^ 2 := by
    field_simp
  have hnumB : F / m * (2 * (c / (2 * m)) * Ω) = F * (c * Ω) / m ^ 2 := by
    field_simp
  rw [hden, hnumA, hnumB, div_div_div_cancel_right₀ (pow_ne_zero 2 hm0),
    div_div_div_cancel_right₀ (pow_ne_zero 2 hm0)]
  exact ⟨rfl, rfl⟩

/-! ## G. The particular response -/

/-- The particular response has velocity `particularVelocity`. -/
lemma hasDerivAt_particularResponse (m c k F Ω t : ℝ) :
    HasDerivAt (particularResponse m c k F Ω) (particularVelocity m c k F Ω t) t := by
  have h1 : HasDerivAt (fun s => Ω * s) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hc := (Real.hasDerivAt_cos (Ω * t)).comp t h1
  have hs := (Real.hasDerivAt_sin (Ω * t)).comp t h1
  have h := (hc.const_mul (steadyStateCos m c k F Ω)).add (hs.const_mul (steadyStateSin m c k F Ω))
  have h' : HasDerivAt (particularResponse m c k F Ω) _ t := h
  exact h'.congr_deriv (by unfold particularVelocity; ring)

/-- The particular velocity has derivative `-Ω ^ 2 x_p (t)`. -/
lemma hasDerivAt_particularVelocity (m c k F Ω t : ℝ) :
    HasDerivAt (particularVelocity m c k F Ω) (-Ω ^ 2 * particularResponse m c k F Ω t) t := by
  have h1 : HasDerivAt (fun s => Ω * s) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hc := (Real.hasDerivAt_cos (Ω * t)).comp t h1
  have hs := (Real.hasDerivAt_sin (Ω * t)).comp t h1
  have h := ((hc.const_mul (steadyStateSin m c k F Ω)).sub
    (hs.const_mul (steadyStateCos m c k F Ω))).const_mul Ω
  have h' : HasDerivAt (particularVelocity m c k F Ω) _ t := h
  exact h'.congr_deriv (by unfold particularResponse; ring)

/-- With a nonzero steady-state denominator the particular response solves
`m x'' + c x' + k x = F cos (Ω t)`. -/
lemma particularResponse_solves {m c k F Ω : ℝ} (hD : steadyStateDenominator m c k Ω ≠ 0)
    (t : ℝ) :
    m * deriv (deriv (particularResponse m c k F Ω)) t +
        c * deriv (particularResponse m c k F Ω) t + k * particularResponse m c k F Ω t =
      F * Real.cos (Ω * t) := by
  have hd : deriv (particularResponse m c k F Ω) = particularVelocity m c k F Ω :=
    funext fun s => (hasDerivAt_particularResponse m c k F Ω s).deriv
  rw [hd, (hasDerivAt_particularVelocity m c k F Ω t).deriv]
  unfold particularResponse particularVelocity steadyStateCos steadyStateSin
  unfold steadyStateDenominator at hD ⊢
  set D := (k - m * Ω ^ 2) ^ 2 + (c * Ω) ^ 2 with hDdef
  field_simp
  rw [hDdef]
  ring

/-! ## H. The forced response -/

/-- The forced response is twice continuously differentiable, solves the forced equation, and
has initial position `x₀` and initial velocity `v₀`. -/
lemma forcedResponse_spec {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) {F Ω : ℝ}
    (hD : steadyStateDenominator m c k Ω ≠ 0) (x₀ v₀ : ℝ) :
    ContDiff ℝ 2 (forcedResponse m c k hm hc hk F Ω x₀ v₀) ∧
      (∀ t, m * deriv (deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀)) t +
          c * deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀) t +
          k * forcedResponse m c k hm hc hk F Ω x₀ v₀ t = F * Real.cos (Ω * t)) ∧
      forcedResponse m c k hm hc hk F Ω x₀ v₀ 0 = x₀ ∧
      deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀) 0 = v₀ := by
  set S := massSpringDamper m c k hm hc hk with hS
  set IC := initialConditions (x₀ - particularResponse m c k F Ω 0)
    (v₀ - particularVelocity m c k F Ω 0) with hIC
  set w := S.trajectory IC with hw
  have hwC : ContDiff ℝ ∞ w := S.trajectory_contDiff IC
  have hwd : Differentiable ℝ w := hwC.differentiable (by simp)
  have hw'd : Differentiable ℝ (∂ₜ w) := Time.deriv_differentiable_of_contDiff w hwC
  have hcoord : ∀ u : Time → EuclideanSpace ℝ (Fin 1), Differentiable ℝ u → ∀ τ : ℝ,
      HasDerivAt (fun t : ℝ => u ⟨t⟩ 0) (∂ₜ u ⟨τ⟩ 0) τ := by
    intro u hu τ
    exact (EuclideanSpace.proj (0 : Fin 1)).hasFDerivAt.comp_hasDerivAt τ
      (Time.hasDerivAt_comp_toRealCLE_symm u τ (hu _))
  set f : ℝ → ℝ := fun t => w ⟨t⟩ 0 with hf
  have hfd : deriv f = fun t => ∂ₜ w ⟨t⟩ 0 := funext fun τ => (hcoord w hwd τ).deriv
  have hfdd : deriv (deriv f) = fun t => ∂ₜ (∂ₜ w) ⟨t⟩ 0 := by
    rw [hfd]
    exact funext fun τ => (hcoord (∂ₜ w) hw'd τ).deriv
  have hfC : ContDiff ℝ 2 f :=
    ((EuclideanSpace.proj (0 : Fin 1)).contDiff.comp
      (hwC.comp Time.toRealCLE.symm.contDiff)).of_le (by simp)
  have hfdiff : Differentiable ℝ f := hfC.differentiable (by norm_num)
  have hfdiff' : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hfC).2.2.differentiable (by norm_num)
  have hEOM : ∀ t : Time, m • ∂ₜ (∂ₜ w) t + c • ∂ₜ w t + k • w t = 0 :=
    S.trajectory_equationOfMotion IC
  have hfEq : ∀ t, m * deriv (deriv f) t + c * deriv f t + k * f t = 0 := by
    intro t
    rw [hfdd, hfd]
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) (hEOM ⟨t⟩)
    simpa using this
  set p := particularResponse m c k F Ω with hp
  have hpC : ContDiff ℝ 2 p := by
    rw [hp]
    unfold particularResponse
    fun_prop
  have hpdiff : Differentiable ℝ p := hpC.differentiable (by norm_num)
  have hpd : deriv p = particularVelocity m c k F Ω :=
    funext fun s => (hasDerivAt_particularResponse m c k F Ω s).deriv
  have hpdiff' : Differentiable ℝ (deriv p) := by
    rw [hpd]
    exact fun s => (hasDerivAt_particularVelocity m c k F Ω s).differentiableAt
  have hxeq : forcedResponse m c k hm hc hk F Ω x₀ v₀ = fun t => p t + f t := rfl
  have hd1 : deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀) = fun t => deriv p t + deriv f t := by
    rw [hxeq]
    funext t
    exact deriv_add (hpdiff t) (hfdiff t)
  have hd2 : deriv (deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀)) =
      fun t => deriv (deriv p) t + deriv (deriv f) t := by
    rw [hd1]
    funext t
    exact deriv_add (hpdiff' t) (hfdiff' t)
  have h0T : (⟨0⟩ : Time) = 0 := by
    ext
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hxeq]
    exact hpC.add hfC
  · intro t
    rw [hd2, hd1, hxeq]
    have h1 := particularResponse_solves (F := F) hD t
    have h2 := hfEq t
    simp only [] at h1 h2 ⊢
    linarith
  · rw [hxeq]
    simp only [hf, hw, h0T, S.trajectory_apply_zero, hIC, initialConditions]
    simp
  · rw [hd1, hfd, hpd]
    simp only [hw, h0T, S.trajectory_velocity_at_zero, hIC, initialConditions]
    simp

/-! ## I. Phase space and uniqueness -/

/-- A `C²` displacement solving the forced equation gives the phase-space solution
`t ↦ (x t, x' t)` of `z' = A z + b (t)`. -/
lemma phase_of_displacement {m c k : ℝ} (hm : 0 < m) (F Ω : ℝ) {x : ℝ → ℝ}
    (hx : ContDiff ℝ 2 x)
    (hEq : ∀ t, m * deriv (deriv x) t + c * deriv x t + k * x t = F * Real.cos (Ω * t))
    (t : ℝ) :
    HasDerivAt (fun s => (x s, deriv x s))
      (phaseOperator m c k (x t, deriv x t) + phaseForcing m F Ω t) t := by
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hxdd : Differentiable ℝ (deriv x) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hx).2.2.differentiable (by norm_num)
  have h : HasDerivAt (fun s => (x s, deriv x s)) (deriv x t, deriv (deriv x) t) t :=
    (hxd t).hasDerivAt.prodMk (hxdd t).hasDerivAt
  refine h.congr_deriv ?_
  have hm0 : m ≠ 0 := hm.ne'
  have hE := hEq t
  simp only [phaseOperator, phaseForcing]
  ext
  · simp
  · simp
    field_simp
    linarith

/-- A phase-space solution of `z' = A z + b (t)` has a `C²` first component, whose derivative is
the second component and which solves the forced equation. -/
lemma displacement_of_phase {m c k : ℝ} (hm : 0 < m) (F Ω : ℝ) {z : ℝ → ℝ × ℝ}
    (hz : ∀ t, HasDerivAt z (phaseOperator m c k (z t) + phaseForcing m F Ω t) t) :
    ContDiff ℝ 2 (fun t : ℝ => (z t).1) ∧ deriv (fun t : ℝ => (z t).1) = (fun t => (z t).2) ∧
      ∀ t : ℝ, m * deriv (deriv (fun s : ℝ => (z s).1)) t + c * deriv (fun s : ℝ => (z s).1) t +
          k * (z t).1 = F * Real.cos (Ω * t) := by
  have hm0 : m ≠ 0 := hm.ne'
  have h1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (z s).1) (z t).2 t := by
    intro t
    have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
    refine h.congr_deriv ?_
    simp [phaseOperator, phaseForcing]
  have h2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (z s).2)
      (-(k / m) * (z t).1 + -(c / m) * (z t).2 + F * Real.cos (Ω * t) / m) t := by
    intro t
    have h := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
    refine h.congr_deriv ?_
    simp [phaseOperator, phaseForcing]
  have hd1 : deriv (fun s : ℝ => (z s).1) = fun s => (z s).2 := funext fun t => (h1 t).deriv
  have hd2 : deriv (fun s : ℝ => (z s).2) =
      fun t : ℝ => -(k / m) * (z t).1 + -(c / m) * (z t).2 + F * Real.cos (Ω * t) / m :=
    funext fun t => (h2 t).deriv
  have hzc : Continuous z := continuous_iff_continuousAt.2 fun t => (hz t).continuousAt
  refine ⟨?_, hd1, ?_⟩
  · refine (contDiff_succ_iff_deriv (n := 1)).mpr ⟨fun t => (h1 t).differentiableAt, by simp, ?_⟩
    rw [hd1]
    refine (contDiff_succ_iff_deriv (n := 0)).mpr ⟨fun t => (h2 t).differentiableAt, by simp, ?_⟩
    rw [hd2, contDiff_zero]
    fun_prop
  · intro t
    rw [hd1, hd2]
    field_simp
    ring

/-- Uniqueness in the `C²` class: a twice continuously differentiable solution of the forced
equation with initial position `x₀` and velocity `v₀` is the forced response. -/
lemma forcedResponse_unique {m c k : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hk : 0 < k) {F Ω : ℝ}
    (hD : steadyStateDenominator m c k Ω ≠ 0) {x₀ v₀ : ℝ} {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hEq : ∀ t, m * deriv (deriv x) t + c * deriv x t + k * x t = F * Real.cos (Ω * t))
    (h0 : x 0 = x₀) (hv0 : deriv x 0 = v₀) :
    x = forcedResponse m c k hm hc hk F Ω x₀ v₀ := by
  obtain ⟨hyC, hyEq, hy0, hyv⟩ := forcedResponse_spec hm hc hk hD x₀ v₀
  have hb : Continuous (phaseForcing m F Ω) := by
    unfold phaseForcing
    fun_prop
  obtain ⟨u, -, -, -, huniq⟩ :=
    MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
      (phaseOperator m c k) (phaseForcing m F Ω) 0 (x₀, v₀) hb
  have e1 := huniq (fun s => (x s, deriv x s)) (by simp [h0, hv0])
    (phase_of_displacement hm F Ω hx hEq)
  have e2 := huniq (fun s => (forcedResponse m c k hm hc hk F Ω x₀ v₀ s,
      deriv (forcedResponse m c k hm hc hk F Ω x₀ v₀) s)) (by simp [hy0, hyv])
    (phase_of_displacement hm F Ω hyC hyEq)
  funext t
  have := congrFun (e1.trans e2.symm) t
  exact (Prod.ext_iff.mp this).1

/-! ## J. Undamped resonance model -/

open Filter

/-- The undamped resonant response `F t sin (ω₀ t) / (2 m ω₀)` of a mass `m` to the force
`F cos (ω₀ t)` at the natural angular frequency `ω₀`. -/
noncomputable def resonantResponse (m ω₀ F t : ℝ) : ℝ :=
  F * t * Real.sin (ω₀ * t) / (2 * m * ω₀)

/-- The velocity `F (sin (ω₀ t) + ω₀ t cos (ω₀ t)) / (2 m ω₀)` of the resonant response. -/
noncomputable def resonantVelocity (m ω₀ F t : ℝ) : ℝ :=
  F * (Real.sin (ω₀ * t) + ω₀ * t * Real.cos (ω₀ * t)) / (2 * m * ω₀)

/-- The envelope-touch times `t_n = (2 π n + π / 2) / ω₀`, at which `sin (ω₀ t_n) = 1`. For
`m, ω₀ > 0` the absolute value of the resonant response meets its envelope `|F| |t| / (2 m ω₀)`
there (`abs_resonantResponse_resonanceEnvelopeTime`). For `F ≠ 0` they are not extrema of the
response: its velocity there is `F / (2 m ω₀) ≠ 0`. -/
noncomputable def resonanceEnvelopeTime (ω₀ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi * n + Real.pi / 2) / ω₀

/-! ## K. The resonance branch -/

/-- Forcing at the angular frequency `ω₀` of `k = m ω₀ ^ 2` is forcing at the convention's natural
frequency `√(k / m)`, and zero damping is the convention's damping rate `0`. -/
lemma resonance_branch_params {m ω₀ k : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀) (hk : k = m * ω₀ ^ 2) :
    atlasNaturalFrequency m k = ω₀ ∧ atlasDamping m 0 = 0 := by
  have hm' : m ≠ 0 := ne_of_gt hm
  constructor
  · have hkm : k / m = ω₀ ^ 2 := by rw [hk]; field_simp
    unfold atlasNaturalFrequency
    rw [hkm]
    exact Real.sqrt_sq (le_of_lt hω₀)
  · unfold atlasDamping
    exact zero_div _

/-- The steady-state denominator `(k - m Ω ^ 2) ^ 2 + (c Ω) ^ 2` vanishes exactly on this
branch: for `k = m ω₀ ^ 2` and a forcing frequency `Ω ≥ 0` it is zero iff `c = 0` and `Ω = ω₀`. -/
lemma steadyStateDenominator_eq_zero_iff {m ω₀ k : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀)
    (hk : k = m * ω₀ ^ 2) {c Ω : ℝ} (hΩ : 0 ≤ Ω) :
    (k - m * Ω ^ 2) ^ 2 + (c * Ω) ^ 2 = 0 ↔ c = 0 ∧ Ω = ω₀ := by
  constructor
  · intro h
    have h1 := sq_nonneg (k - m * Ω ^ 2)
    have h2 := sq_nonneg (c * Ω)
    have hA : (k - m * Ω ^ 2) ^ 2 = 0 := by linarith
    have hB : (c * Ω) ^ 2 = 0 := by linarith
    have hA' : k - m * Ω ^ 2 = 0 := sq_eq_zero_iff.mp hA
    have hB' : c * Ω = 0 := sq_eq_zero_iff.mp hB
    have hm' : m ≠ 0 := ne_of_gt hm
    have hΩ2 : Ω ^ 2 = ω₀ ^ 2 := by
      have hmeq : m * Ω ^ 2 = m * ω₀ ^ 2 := by rw [hk] at hA'; linarith
      exact mul_left_cancel₀ hm' hmeq
    have hΩω : Ω = ω₀ ∨ Ω = -ω₀ := sq_eq_sq_iff_eq_or_eq_neg.mp hΩ2
    have hΩpos : Ω = ω₀ := by
      rcases hΩω with h | h
      · exact h
      · exfalso; rw [h] at hΩ; linarith [hω₀]
    have hc : c = 0 := by
      rw [hΩpos] at hB'
      exact (mul_eq_zero.mp hB').resolve_right (ne_of_gt hω₀)
    exact ⟨hc, hΩpos⟩
  · rintro ⟨rfl, rfl⟩
    rw [hk]
    simp

/-! ## L. Resonant derivatives and equation of motion -/

/-- The resonant response has velocity `resonantVelocity`: the product rule on the secular
factor `t` and the chain rule on `sin (ω₀ t)`. -/
lemma hasDerivAt_resonantResponse (m ω₀ F t : ℝ) :
    HasDerivAt (resonantResponse m ω₀ F) (resonantVelocity m ω₀ F t) t := by
  have h1 : HasDerivAt (fun t : ℝ => F * t) (F * 1) t := (hasDerivAt_id' t).const_mul F
  have haff : HasDerivAt (fun t : ℝ => ω₀ * t) (ω₀ * 1) t := (hasDerivAt_id' t).const_mul ω₀
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (ω₀ * t)) (Real.cos (ω₀ * t) * (ω₀ * 1)) t :=
    (Real.hasDerivAt_sin (ω₀ * t)).comp t haff
  have h4 := (h1.mul h2).div_const (2 * m * ω₀)
  unfold resonantResponse resonantVelocity
  convert h4 using 1
  ring

/-- The resonant velocity has derivative `F (2 ω₀ cos (ω₀ t) - ω₀ ^ 2 t sin (ω₀ t)) / (2 m ω₀)`. -/
lemma hasDerivAt_resonantVelocity (m ω₀ F t : ℝ) :
    HasDerivAt (resonantVelocity m ω₀ F)
      (F * (2 * ω₀ * Real.cos (ω₀ * t) - ω₀ ^ 2 * t * Real.sin (ω₀ * t)) / (2 * m * ω₀)) t := by
  have haff : HasDerivAt (fun t : ℝ => ω₀ * t) (ω₀ * 1) t := (hasDerivAt_id' t).const_mul ω₀
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (ω₀ * t)) (Real.cos (ω₀ * t) * (ω₀ * 1)) t :=
    (Real.hasDerivAt_sin (ω₀ * t)).comp t haff
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (ω₀ * t)) ((-Real.sin (ω₀ * t)) * (ω₀ * 1)) t :=
    (Real.hasDerivAt_cos (ω₀ * t)).comp t haff
  have hprod := haff.mul hcos
  have hadd := hsin.add hprod
  have hF := hadd.const_mul F
  have h4 := hF.div_const (2 * m * ω₀)
  unfold resonantVelocity
  convert h4 using 1
  ring

/-- The resonant response solves `m x'' + k x = F cos (ω₀ t)` for `k = m ω₀ ^ 2`. -/
lemma resonantResponse_solves {m ω₀ k : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀) (hk : k = m * ω₀ ^ 2)
    (F t : ℝ) :
    m * deriv (deriv (resonantResponse m ω₀ F)) t + k * resonantResponse m ω₀ F t =
      F * Real.cos (ω₀ * t) := by
  have h1 : deriv (resonantResponse m ω₀ F) = resonantVelocity m ω₀ F :=
    funext fun t => (hasDerivAt_resonantResponse m ω₀ F t).deriv
  rw [h1, (hasDerivAt_resonantVelocity m ω₀ F t).deriv]
  have hm' : m ≠ 0 := ne_of_gt hm
  have hω' : ω₀ ≠ 0 := ne_of_gt hω₀
  unfold resonantResponse
  rw [hk]
  field_simp
  ring

/-- The resonant response starts from rest at the origin. -/
lemma resonantResponse_initial (m ω₀ F : ℝ) :
    resonantResponse m ω₀ F 0 = 0 ∧ deriv (resonantResponse m ω₀ F) 0 = 0 := by
  constructor
  · unfold resonantResponse
    simp
  · rw [(hasDerivAt_resonantResponse m ω₀ F 0).deriv]
    unfold resonantVelocity
    simp

/-! ## M. Unbounded amplitude -/

/-- The envelope of the resonant response is `|F| |t| / (2 m ω₀)`. -/
lemma abs_resonantResponse_le {m ω₀ : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀) (F t : ℝ) :
    |resonantResponse m ω₀ F t| ≤ |F| * |t| / (2 * m * ω₀) := by
  have hD : 0 < 2 * m * ω₀ := by positivity
  unfold resonantResponse
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hD, div_le_div_iff_of_pos_right hD]
  have h := Real.abs_sin_le_one (ω₀ * t)
  calc |F| * |t| * |Real.sin (ω₀ * t)| ≤ |F| * |t| * 1 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = |F| * |t| := mul_one _

/-- At the envelope-touch times the resonant response takes the signed value
`F t_n / (2 m ω₀)`. -/
lemma resonantResponse_resonanceEnvelopeTime {ω₀ : ℝ} (hω₀ : 0 < ω₀) (m F : ℝ) (n : ℕ) :
    resonantResponse m ω₀ F (resonanceEnvelopeTime ω₀ n) =
      F * resonanceEnvelopeTime ω₀ n / (2 * m * ω₀) := by
  have hω' : ω₀ ≠ 0 := ne_of_gt hω₀
  have harg : ω₀ * resonanceEnvelopeTime ω₀ n = 2 * Real.pi * n + Real.pi / 2 := by
    unfold resonanceEnvelopeTime
    field_simp
  have hsin : Real.sin (2 * Real.pi * (n : ℝ) + Real.pi / 2) = 1 := by
    have h : (2 * Real.pi * (n : ℝ) + Real.pi / 2) = Real.pi / 2 + n * (2 * Real.pi) := by ring
    rw [h, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  unfold resonantResponse
  rw [harg, hsin]
  ring

/-- Envelope contact: for `m, ω₀ > 0`, at the envelope-touch times the absolute value of the
resonant response equals the envelope `|F| |t| / (2 m ω₀)` of `abs_resonantResponse_le`, so the
envelope is attained there. -/
lemma abs_resonantResponse_resonanceEnvelopeTime {m ω₀ : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀) (F : ℝ)
    (n : ℕ) :
    |resonantResponse m ω₀ F (resonanceEnvelopeTime ω₀ n)| =
      |F| * |resonanceEnvelopeTime ω₀ n| / (2 * m * ω₀) := by
  rw [resonantResponse_resonanceEnvelopeTime hω₀ m F n, abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * m * ω₀)]

/-- The envelope-touch times tend to infinity. -/
lemma tendsto_resonanceEnvelopeTime {ω₀ : ℝ} (hω₀ : 0 < ω₀) :
    Tendsto (resonanceEnvelopeTime ω₀) atTop atTop := by
  have hω' : ω₀ ≠ 0 := ne_of_gt hω₀
  have hbase :
      Tendsto (fun n : ℕ => (2 * Real.pi / ω₀) * (n : ℝ) + (Real.pi / 2) / ω₀) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul_atTop (show (0 : ℝ) < 2 * Real.pi / ω₀ by positivity)
    exact tendsto_atTop_add_const_right _ _ h2
  have heq : resonanceEnvelopeTime ω₀ =
      fun n : ℕ => (2 * Real.pi / ω₀) * (n : ℝ) + (Real.pi / 2) / ω₀ := by
    funext n
    unfold resonanceEnvelopeTime
    field_simp
  rw [heq]
  exact hbase

/-- Unbounded amplitude: for `F ≠ 0` the amplitude at the envelope-touch times tends to
infinity. -/
lemma tendsto_abs_resonantResponse_resonanceEnvelopeTime {m ω₀ F : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀)
    (hF : F ≠ 0) :
    Tendsto (fun n : ℕ => |resonantResponse m ω₀ F (resonanceEnvelopeTime ω₀ n)|) atTop atTop := by
  have hD : 0 < 2 * m * ω₀ := by positivity
  have htime : ∀ n : ℕ, 0 < resonanceEnvelopeTime ω₀ n := by
    intro n
    unfold resonanceEnvelopeTime
    apply div_pos _ hω₀
    positivity
  have heq : (fun n : ℕ => |resonantResponse m ω₀ F (resonanceEnvelopeTime ω₀ n)|) =
      fun n : ℕ => (|F| / (2 * m * ω₀)) * resonanceEnvelopeTime ω₀ n := by
    funext n
    rw [abs_resonantResponse_resonanceEnvelopeTime hm hω₀ F n, abs_of_pos (htime n)]
    ring
  rw [heq]
  exact (tendsto_resonanceEnvelopeTime hω₀).const_mul_atTop (div_pos (abs_pos.mpr hF) hD)

/-! ## N. Damping leaves the branch -/

/-- With nonzero damping `c` and nonzero force amplitude the resonant response does not solve
`m x'' + c x' + k x = F cos (ω₀ t)`. -/
lemma resonantResponse_not_solves_damped {m ω₀ k : ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀)
    (hk : k = m * ω₀ ^ 2) {c F : ℝ} (hc : c ≠ 0) (hF : F ≠ 0) :
    ¬ ∀ t, m * deriv (deriv (resonantResponse m ω₀ F)) t + c * deriv (resonantResponse m ω₀ F) t +
        k * resonantResponse m ω₀ F t = F * Real.cos (ω₀ * t) := by
  intro h
  have hsol : ∀ t, m * deriv (deriv (resonantResponse m ω₀ F)) t +
      k * resonantResponse m ω₀ F t = F * Real.cos (ω₀ * t) :=
    fun t => resonantResponse_solves hm hω₀ hk F t
  have hcx : ∀ t, c * deriv (resonantResponse m ω₀ F) t = 0 := by
    intro t
    have h1 := h t
    have h2 := hsol t
    linarith
  have hderiv : deriv (resonantResponse m ω₀ F) = resonantVelocity m ω₀ F :=
    funext fun t => (hasDerivAt_resonantResponse m ω₀ F t).deriv
  have hω' : ω₀ ≠ 0 := ne_of_gt hω₀
  set t₀ : ℝ := Real.pi / 2 / ω₀ with ht₀
  have hωt₀ : ω₀ * t₀ = Real.pi / 2 := by
    rw [ht₀]
    field_simp
  have hx' : deriv (resonantResponse m ω₀ F) t₀ ≠ 0 := by
    rw [hderiv]
    unfold resonantVelocity
    rw [hωt₀, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, add_zero, mul_one]
    exact div_ne_zero hF (ne_of_gt (by positivity : (0 : ℝ) < 2 * m * ω₀))
  have h0 := hcx t₀
  rw [mul_eq_zero] at h0
  exact hx' (h0.resolve_left hc)

end PhyslibExt.Mechanics.OscillatorResponse
