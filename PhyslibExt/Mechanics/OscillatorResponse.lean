/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Solution
public import PhyslibExt.Units.EngineeringQuantities

/-!
# Damping and forcing parameter correspondence

An engineering mass-spring-damper has mass `m > 0`, viscous damping coefficient `c ≥ 0`
(force per velocity) and stiffness `k > 0` (force per length):

  `m x'' + c x' + k x = F cos (Ω t)`,

with initial position `x₀`, initial velocity `v₀` and a forcing amplitude `F` in force units.
This module maps these parameters to Physlib's damped harmonic oscillator and to the
forced-oscillator convention `x'' + 2 γ x' + ω₀ ^ 2 x = F cos (Ω t)`.

## i. Overview

Physlib's damped oscillator takes the damping coefficient `γ = c` itself
(`massSpringDamper`); its equation of motion is the free equation above, its regime is read
off `c ^ 2 - 4 m k`, and its selected free trajectory is the unique smooth solution with the
given initial position and velocity. The forced-oscillator convention uses `γ = c / (2 m)`,
`ω₀ = √(k / m)` and the forcing amplitude `F / m`, which is an acceleration, not a force. The
two damping conventions differ by the factor `2 m`, and `k = 0` is not a Physlib oscillator.
Physlib's uniqueness statement is for smooth (`ContDiff ℝ ∞`) trajectories. Parameters,
forcing and initial data are model inputs.

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

## iii. Table of contents

- A. Model
- B. Parameter map
- C. Regimes, free trajectories and dissipation
- D. Force units

## iv. References

- S. S. Rao, *Mechanical Vibrations*, 6th edition, chapters 2-3 (viscously damped free and
  harmonically forced single-degree-of-freedom systems).
- L. D. Landau and E. M. Lifshitz, *Mechanics*, §25 (damped oscillations).
- `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` and `.Solution`: the carrier,
  equation of motion, regimes, energy dissipation and selected trajectory reused here.
- `PhyslibExt.EarthScience.DampedOscillator`: the forced-oscillator convention
  `x'' + 2 γ x' + ω₀ ^ 2 x = F cos (ω t)`.
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

end PhyslibExt.Mechanics.OscillatorResponse
