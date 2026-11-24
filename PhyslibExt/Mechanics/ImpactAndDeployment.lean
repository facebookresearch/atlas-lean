/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Robotics.Hybrid.DwellDivergence
public import PhyslibExt.Mechanics.PowerPorts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Instantaneous impact events and the bouncing ball

Two bodies of masses `m₁, m₂ > 0` move on one line and collide instantaneously, or one body of
mass `m > 0` meets a stationary wall. Velocities are components along the line of the impact:
`v₁, v₂` (or `v⁻`) just before the event and `u₁, u₂` (or `v⁺`) just after it. A ball bouncing on a
fixed floor chains fixed-wall events and ballistic flights.

## i. Overview

The event map solves momentum conservation `m₁ u₁ + m₂ u₂ = m₁ v₁ + m₂ v₂` together with
Newton's restitution law `u₂ - u₁ = -e (v₂ - v₁)`, and the solution is unique. For every real `e`
the kinetic energy `K` of the pair satisfies the identity
`K⁻ - K⁺ = (1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`. Its sign needs the range of the
coefficient of restitution: for `e ∈ [0, 1]` the kinetic energy does not rise, for `e = 1` it is
kept, and for `e > 1` with a nonzero relative velocity it would rise, which puts `e > 1` outside
the model.

During the event body 1 receives the impulse `J = -(1 + e) μ (v₁ - v₂)`, with the reduced mass
`μ = m₁ m₂ / (m₁ + m₂)`, and body 2 receives `-J`, for every real `e`; each momentum jump is the
impulse received, the event form of the impulse identity of `PhyslibExt.Mechanics.PowerPorts`.
After the event each body follows the actual constant-force trajectory of that module started at
its post-impact velocity: for every real `e` the total momentum is the pre-impact total plus the
external impulse, and in free flight the kinetic energy stays at its pre-impact value minus
`(1 - e²) μ (v₁ - v₂)² / 2`.

At a fixed wall the normal axis points from the wall into the body's side, and the event maps the
normal velocity `v⁻` to `v⁺ = -e v⁻`. For every real `e` the wall impulse is
`J = m (v⁺ - v⁻) = -(1 + e) m v⁻`, the body's momentum jumps by exactly `J`, its kinetic energy
changes by `K⁺ - K⁻ = -(1 - e²) m v⁻² / 2`, and after the event, on the same constant-force
trajectory from `v⁺`, its momentum at time `t` is `m v⁻ + J + t F`. The sign conclusions need
`e ≥ 0`: an incoming body (`v⁻ < 0`) then leaves the wall, or rests on it exactly when `e = 0`,
and the impulse `J` points out of the wall; for `v⁻ ≠ 0` the body alone does not conserve
momentum, and its kinetic energy falls exactly when `e < 1`, is kept exactly when `e = 1` and
rises exactly when `e > 1`.

A bouncing ball (sections G-J) leaves the floor, a fixed wall whose normal axis points up, with
upward speed `u > 0` and flies under its weight `-(m g)`, `g > 0`, on the constant-force trajectory
`t u - g t ^ 2 / 2`. It stays above the floor until `T = 2 u / g` and arrives with normal velocity
`-u`; the fixed-wall event gives the next take-off speed `e u`. Chaining arcs and events gives the
take-off speeds `u_n = e ^ n u₀` and the flight durations `T_n = (2 u₀ / g) e ^ n`. Arc `n` is
active (`IsActiveArc`) when its take-off speed is positive; every active arc is such a flight
(`bounce_arc`), and the contacts are the ends of the active arcs: the contact after arc `n` is at
the elapsed time `dwellElapsed T (n + 1) = ∑_{k ≤ n} T_k` of
`MathlibExt.Robotics.Hybrid.DwellDivergence`. For `e > 0` every arc is active, so every elapsed time
`dwellElapsed T N` with `N ≥ 1` is a contact time. For `0 < e < 1` the durations sum to
`t_∞ = 2 u₀ / (g (1 - e))`, and the contact times increase strictly, stay below `t_∞` and tend to
it: infinitely many impacts occur before a finite time (Zeno accumulation), while the take-off
speeds tend to `0`. For `e ≥ 0` the durations are summable exactly when `e < 1`. Any sequence of
step durations with a positive lower bound `δ` has only finitely many events up to a finite horizon
(`Robotics.Hybrid.events_finite_of_dwell` of `MathlibExt.Robotics.Hybrid.DwellDivergence`), so the
Zeno family has no such bound. For `e = 1` every flight lasts `2 u₀ / g` and finitely many impacts
occur on every finite horizon. For `e = 0` the motion terminates: the first arc is the only active
one, a ballistic flight that lands at `2 u₀ / g` with velocity `-u₀` (`bounce_arc`), and the ball
then rests on the floor, with every later take-off speed and flight duration `0` and the elapsed
time constant.

Model inputs: a one-dimensional isolated two-body instantaneous impact, with no external impulse
during the event, or one body at a fixed wall; `e` is the coefficient of restitution. The event
maps, the impulses and the energy identities hold for every real `e`; only the sign conclusions
use a range, `e ∈ [0, 1]` for two bodies (and `e > 1` for the excluded gain) and `e ≥ 0` at the
wall. The bouncing ball is a model of explicit piecewise ballistic arcs between instantaneous
fixed-wall events, with `g > 0`. Contact forces during the impact, oblique or rotational impact,
multiple simultaneous contacts, event detection for general guards, a global trajectory with a
classical derivative at the impacts, any motion at or after the accumulation time (post-Zeno
continuation), and empirical adequacy or system safety are not treated. The fixed wall is an
external-impulse model with one normal direction, not a limit of the finite-mass collision.

## ii. Key results

- `impact_solve_iff`: for every real `e`, the event map is the unique solution of momentum
  conservation and the restitution law.
- `impact_energy_loss`: for every real `e`, the kinetic-energy identity
  `K⁻ - K⁺ = (1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`.
- `impact_energy_le`, `impact_energy_eq_of_elastic`, `impact_energy_lt_of_one_lt`: no gain for
  `e ∈ [0, 1]`, conservation for `e = 1`, and a gain for `e > 1` with a nonzero relative
  velocity.
- `impact_impulse`: equal and opposite event impulses, for every real `e`.
- `impact_then_flight_momentum`, `impact_then_free_flight_energy`: momentum and kinetic energy
  across the event and the following constant-force phase, for every real `e`.
- `wallImpulse_eq`, `wall_energy_change`: the wall impulse `-(1 + e) m v⁻` and the body's
  kinetic-energy change, for every real `e`.
- `wallReboundVelocity_nonneg`, `wallImpulse_pos`, `body_momentum_ne`: for `e ≥ 0`, the rebound
  direction, the outward impulse and the body's momentum change.
- `wall_energy_cases`: for `e ≥ 0` and `v⁻ ≠ 0`, the sign of the body's kinetic-energy change in
  each of the cases `e < 1`, `e = 1` and `e > 1`.
- `rebound_then_flight_momentum`: for every real `e`, the wall impulse and the impulse of the
  following constant-force phase in one momentum balance.
- `bounceSpeed_eq`, `flightDuration_eq`, `bounce_arc`: the take-off speeds `e ^ n u₀` and the
  flight durations `(2 u₀ / g) e ^ n`; each active arc has a positive duration, lands at it with
  velocity `-u_n`, stays above the floor before, and the wall event gives the next take-off speed.
- `IsActiveArc`, `isActiveArc_of_pos`: an arc is active when its take-off speed is positive; for
  `e > 0` and `u₀ > 0` every arc is active.
- `hasSum_flightDuration`, `zeno_accumulation`, `summable_flightDuration_iff`: for `0 < e < 1` the
  durations sum to `2 u₀ / (g (1 - e))` and the contact times accumulate there; for `e ≥ 0` the
  durations are summable exactly when `e < 1`.
- `zeno_no_dwell`: the Zeno family has no positive dwell-time lower bound, the hypothesis of the
  finite-event criterion `Robotics.Hybrid.events_finite_of_dwell`.
- `elastic_events_finite`, `inelastic_stops`: for `e = 1` finitely many impacts on every horizon;
  for `e = 0` the first arc is the only active one, and the motion terminates after the first
  impact at `2 u₀ / g`.

## iii. Table of contents

- A. The two-body event map
- B. Kinetic energy across the event
- C. Event ports and the continuous phase
- D. The fixed-wall event
- E. Kinetic energy of the body
- F. The wall impulse and the continuous phase
- G. Ballistic arcs and the bounce sequence
- H. The finite sum and Zeno accumulation
- I. No dwell-time lower bound for the Zeno family
- J. The boundary cases `e = 1` and `e = 0`

## iv. References

- F. P. Beer and E. R. Johnston Jr., *Vector Mechanics for Engineers: Dynamics*, chapters 11 and
  13 (projectile motion; direct central impact, coefficient of restitution).
- R. C. Hibbeler, *Engineering Mechanics: Dynamics*, 14th edition, chapter 15 (impact,
  coefficient of restitution).
- W. J. Stronge, *Impact Mechanics*, chapter 1 (Newton's coefficient of restitution and the
  energy loss of a direct collision).
- K. H. Johansson, M. Egerstedt, J. Lygeros and S. Sastry, *On the regularization of Zeno hybrid
  automata*, Systems & Control Letters 38 (1999): the bouncing ball as a Zeno hybrid system.
- R. Goebel, R. G. Sanfelice and A. R. Teel, *Hybrid Dynamical Systems*, Princeton University
  Press (2012): dwell-time conditions and finitely many jumps on bounded time intervals.
- `PhyslibExt.Mechanics.PowerPorts`: the constant-force trajectory and the impulse identity.
- `MathlibExt.Robotics.Hybrid.DwellDivergence`: the elapsed time of a duration sequence, its
  linear lower bound under a dwell time, and the finite-event criterion.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.ImpactAndDeployment

open PhyslibExt.Mechanics.PowerPorts

/-! ## A. The two-body event map -/

/-- Velocity of body 1 just after the event, from the velocities `v₁, v₂` just before it:
`(m₁ v₁ + m₂ v₂ - m₂ e (v₁ - v₂)) / (m₁ + m₂)`. -/
noncomputable def impactVelocity₁ (m₁ m₂ e v₁ v₂ : ℝ) : ℝ :=
  (m₁ * v₁ + m₂ * v₂ - m₂ * e * (v₁ - v₂)) / (m₁ + m₂)

/-- Velocity of body 2 just after the event: `(m₁ v₁ + m₂ v₂ + m₁ e (v₁ - v₂)) / (m₁ + m₂)`. -/
noncomputable def impactVelocity₂ (m₁ m₂ e v₁ v₂ : ℝ) : ℝ :=
  (m₁ * v₁ + m₂ * v₂ + m₁ * e * (v₁ - v₂)) / (m₁ + m₂)

/-- The post-impact velocities `u₁, u₂` satisfy momentum conservation and Newton's restitution
law exactly when they are the event map. -/
lemma impact_solve_iff {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (e v₁ v₂ u₁ u₂ : ℝ) :
    (m₁ * u₁ + m₂ * u₂ = m₁ * v₁ + m₂ * v₂ ∧ u₂ - u₁ = -e * (v₂ - v₁)) ↔
      (u₁ = impactVelocity₁ m₁ m₂ e v₁ v₂ ∧ u₂ = impactVelocity₂ m₁ m₂ e v₁ v₂) := by
  have hS : m₁ + m₂ ≠ 0 := ne_of_gt (add_pos hm₁ hm₂)
  constructor
  · rintro ⟨hMom, hRest⟩
    constructor
    · unfold impactVelocity₁
      rw [eq_div_iff hS]
      linear_combination hMom - m₂ * hRest
    · unfold impactVelocity₂
      rw [eq_div_iff hS]
      linear_combination hMom + m₁ * hRest
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp only [impactVelocity₁, impactVelocity₂]
    constructor <;> field_simp <;> ring

/-! ## B. Kinetic energy across the event -/

/-- Kinetic energy `m₁ v₁² / 2 + m₂ v₂² / 2` of the pair. -/
noncomputable def pairKineticEnergy (m₁ m₂ v₁ v₂ : ℝ) : ℝ :=
  m₁ * v₁ ^ 2 / 2 + m₂ * v₂ ^ 2 / 2

/-- Energy loss of the event: `(1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`. -/
lemma impact_energy_loss {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (e v₁ v₂ : ℝ) :
    pairKineticEnergy m₁ m₂ v₁ v₂ -
        pairKineticEnergy m₁ m₂ (impactVelocity₁ m₁ m₂ e v₁ v₂) (impactVelocity₂ m₁ m₂ e v₁ v₂) =
      (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) * (v₁ - v₂) ^ 2 := by
  have hS : m₁ + m₂ ≠ 0 := ne_of_gt (add_pos hm₁ hm₂)
  simp only [pairKineticEnergy, impactVelocity₁, impactVelocity₂]
  field_simp
  ring

/-- For `e ∈ [0, 1]` the event does not increase the kinetic energy. -/
lemma impact_energy_le {m₁ m₂ e : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (v₁ v₂ : ℝ) :
    pairKineticEnergy m₁ m₂ (impactVelocity₁ m₁ m₂ e v₁ v₂) (impactVelocity₂ m₁ m₂ e v₁ v₂) ≤
      pairKineticEnergy m₁ m₂ v₁ v₂ := by
  have h := impact_energy_loss hm₁ hm₂ e v₁ v₂
  have h1 : (0 : ℝ) ≤ 1 - e := sub_nonneg.mpr he₁
  have h2 : (0 : ℝ) ≤ 1 + e := by linarith
  have h3 : (0 : ℝ) ≤ (1 - e) * (1 + e) := mul_nonneg h1 h2
  have he2 : (0 : ℝ) ≤ 1 - e ^ 2 := by nlinarith [h3]
  have hfrac : (0 : ℝ) ≤ (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) := by
    refine div_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg he2 hm₁.le) hm₂.le
    · positivity
  have hsq : (0 : ℝ) ≤ (v₁ - v₂) ^ 2 := sq_nonneg _
  have hnn : (0 : ℝ) ≤ (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) * (v₁ - v₂) ^ 2 :=
    mul_nonneg hfrac hsq
  linarith

/-- An elastic event, `e = 1`, conserves the kinetic energy. -/
lemma impact_energy_eq_of_elastic {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (v₁ v₂ : ℝ) :
    pairKineticEnergy m₁ m₂ (impactVelocity₁ m₁ m₂ 1 v₁ v₂) (impactVelocity₂ m₁ m₂ 1 v₁ v₂) =
      pairKineticEnergy m₁ m₂ v₁ v₂ := by
  have h := impact_energy_loss hm₁ hm₂ 1 v₁ v₂
  norm_num at h
  linarith

/-- A coefficient `e > 1` would inject kinetic energy whenever the relative velocity is
nonzero. -/
lemma impact_energy_lt_of_one_lt {m₁ m₂ e v₁ v₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (he : 1 < e)
    (hv : v₁ ≠ v₂) :
    pairKineticEnergy m₁ m₂ v₁ v₂ <
      pairKineticEnergy m₁ m₂ (impactVelocity₁ m₁ m₂ e v₁ v₂) (impactVelocity₂ m₁ m₂ e v₁ v₂) := by
  have h := impact_energy_loss hm₁ hm₂ e v₁ v₂
  have he2 : (1 : ℝ) - e ^ 2 < 0 := by nlinarith [sq_nonneg (e - 1), he]
  have hnum : (1 - e ^ 2) * m₁ * m₂ < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos he2 hm₁) hm₂
  have hden : (0 : ℝ) < 2 * (m₁ + m₂) := by positivity
  have hfrac : (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  have hne : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hv
  have hsq : (0 : ℝ) < (v₁ - v₂) ^ 2 := by positivity
  have hneg : (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) * (v₁ - v₂) ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hfrac hsq
  linarith

/-! ## C. Event ports and the continuous phase -/

/-- Impulse port of the event: the momentum jump of body 1 is
`J = -(1 + e) m₁ m₂ / (m₁ + m₂) (v₁ - v₂)` and that of body 2 is `-J`. -/
lemma impact_impulse {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (e v₁ v₂ : ℝ) :
    m₁ * impactVelocity₁ m₁ m₂ e v₁ v₂ - m₁ * v₁ =
        -(1 + e) * (m₁ * m₂ / (m₁ + m₂)) * (v₁ - v₂) ∧
      m₂ * impactVelocity₂ m₁ m₂ e v₁ v₂ - m₂ * v₂ =
        (1 + e) * (m₁ * m₂ / (m₁ + m₂)) * (v₁ - v₂) := by
  have hS : m₁ + m₂ ≠ 0 := ne_of_gt (add_pos hm₁ hm₂)
  simp only [impactVelocity₁, impactVelocity₂]
  constructor <;> field_simp <;> ring

/-- Momentum across the event and the following continuous phase: after the event body `i`
follows the actual constant-force trajectory with initial velocity its post-impact velocity and
external force `Fᵢ`; at time `t` after the event the total momentum is the pre-impact total plus
the external impulse `t (F₁ + F₂)`. -/
lemma impact_then_flight_momentum {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (e v₁ v₂ F₁ F₂ t : ℝ) :
    m₁ * constForceVelocity m₁ (impactVelocity₁ m₁ m₂ e v₁ v₂) F₁ t +
        m₂ * constForceVelocity m₂ (impactVelocity₂ m₁ m₂ e v₁ v₂) F₂ t =
      m₁ * v₁ + m₂ * v₂ + t * (F₁ + F₂) := by
  have hS : m₁ + m₂ ≠ 0 := ne_of_gt (add_pos hm₁ hm₂)
  have h1 : m₁ ≠ 0 := ne_of_gt hm₁
  have h2 : m₂ ≠ 0 := ne_of_gt hm₂
  have hmom : m₁ * impactVelocity₁ m₁ m₂ e v₁ v₂ + m₂ * impactVelocity₂ m₁ m₂ e v₁ v₂ =
      m₁ * v₁ + m₂ * v₂ := by
    simp only [impactVelocity₁, impactVelocity₂]
    field_simp
    ring
  have e1 : m₁ * ((t / m₁) * F₁) = t * F₁ := by
    field_simp
  have e2 : m₂ * ((t / m₂) * F₂) = t * F₂ := by
    field_simp
  simp only [constForceVelocity, smul_eq_mul]
  rw [mul_add, mul_add, e1, e2]
  linear_combination hmom

/-- Energy across the event and a free flight: with no external force, the kinetic energy at
every time `t` after the event is the pre-impact kinetic energy minus the event loss. -/
lemma impact_then_free_flight_energy {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (e v₁ v₂ t : ℝ) :
    pairKineticEnergy m₁ m₂ (constForceVelocity m₁ (impactVelocity₁ m₁ m₂ e v₁ v₂) 0 t)
        (constForceVelocity m₂ (impactVelocity₂ m₁ m₂ e v₁ v₂) 0 t) =
      pairKineticEnergy m₁ m₂ v₁ v₂ - (1 - e ^ 2) * m₁ * m₂ / (2 * (m₁ + m₂)) * (v₁ - v₂) ^ 2 := by
  have h := impact_energy_loss hm₁ hm₂ e v₁ v₂
  have z1 : constForceVelocity m₁ (impactVelocity₁ m₁ m₂ e v₁ v₂) 0 t =
      impactVelocity₁ m₁ m₂ e v₁ v₂ := by
    simp [constForceVelocity]
  have z2 : constForceVelocity m₂ (impactVelocity₂ m₁ m₂ e v₁ v₂) 0 t =
      impactVelocity₂ m₁ m₂ e v₁ v₂ := by
    simp [constForceVelocity]
  rw [z1, z2]
  linarith

/-! ## D. The fixed-wall event -/

/-- Normal velocity just after the impact on a stationary wall, `v⁺ = -e v⁻`. -/
def wallReboundVelocity (e v : ℝ) : ℝ :=
  -e * v

/-- Impulse of the wall on a body of mass `m`, `J = m (v⁺ - v⁻)`. -/
def wallImpulse (m e v : ℝ) : ℝ :=
  m * (wallReboundVelocity e v - v)

/-- For `e ≥ 0` an incoming body leaves the wall or rests on it: `v⁺ ≥ 0`, with `v⁺ > 0` exactly
when `e > 0`. -/
lemma wallReboundVelocity_nonneg {e v : ℝ} (he : 0 ≤ e) (hv : v < 0) :
    0 ≤ wallReboundVelocity e v ∧ (0 < wallReboundVelocity e v ↔ 0 < e) := by
  unfold wallReboundVelocity
  constructor
  · have h : e * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he (le_of_lt hv)
    linarith
  · constructor
    · intro hpos
      by_contra hc
      push Not at hc
      have hnn : 0 ≤ e * v := mul_nonneg_of_nonpos_of_nonpos hc (le_of_lt hv)
      linarith
    · intro hpos
      have hneg : e * v < 0 := mul_neg_of_pos_of_neg hpos hv
      linarith

/-- The wall impulse is `J = -(1 + e) m v⁻`. -/
lemma wallImpulse_eq (m e v : ℝ) : wallImpulse m e v = -((1 + e) * m * v) := by
  unfold wallImpulse wallReboundVelocity
  ring

/-- For `e ≥ 0` and an incoming body the wall impulse points out of the wall. -/
lemma wallImpulse_pos {m e v : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hv : v < 0) :
    0 < wallImpulse m e v := by
  rw [wallImpulse_eq]
  have h1 : (0 : ℝ) < (1 + e) * m := mul_pos (by linarith) hm
  have h2 : (1 + e) * m * v < 0 := mul_neg_of_pos_of_neg h1 hv
  linarith

/-- The body alone does not conserve momentum: for `e ≥ 0` and `v⁻ ≠ 0` its momentum changes. -/
lemma body_momentum_ne {m e v : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hv : v ≠ 0) :
    m * wallReboundVelocity e v ≠ m * v := by
  unfold wallReboundVelocity
  intro h
  have hm' : m ≠ 0 := ne_of_gt hm
  have h2 : -e * v = v := mul_left_cancel₀ hm' h
  have h3 : v * (1 + e) = 0 := by linear_combination -h2
  have hpos : (0 : ℝ) < 1 + e := by linarith
  have h4 : (1 : ℝ) + e ≠ 0 := ne_of_gt hpos
  rcases mul_eq_zero.mp h3 with h5 | h5
  · exact hv h5
  · exact absurd h5 h4

/-! ## E. Kinetic energy of the body -/

/-- Kinetic energy `m v² / 2` of the body. -/
noncomputable def bodyKineticEnergy (m v : ℝ) : ℝ :=
  m * v ^ 2 / 2

/-- Exact kinetic-energy change of the event: `K⁺ - K⁻ = -(1 - e²) m v⁻² / 2`. -/
lemma wall_energy_change (m e v : ℝ) :
    bodyKineticEnergy m (wallReboundVelocity e v) - bodyKineticEnergy m v =
      -((1 - e ^ 2) * m * v ^ 2 / 2) := by
  unfold bodyKineticEnergy wallReboundVelocity
  ring

/-- Restitution sign cases for `e ≥ 0` and `v⁻ ≠ 0`: strict loss exactly when `e < 1`, no loss
exactly when `e = 1`, and a gain exactly when `e > 1`. -/
lemma wall_energy_cases {m e v : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hv : v ≠ 0) :
    (bodyKineticEnergy m (wallReboundVelocity e v) < bodyKineticEnergy m v ↔ e < 1) ∧
      (bodyKineticEnergy m (wallReboundVelocity e v) = bodyKineticEnergy m v ↔ e = 1) ∧
      (bodyKineticEnergy m v < bodyKineticEnergy m (wallReboundVelocity e v) ↔ 1 < e) := by
  have hdiff := wall_energy_change m e v
  have hv2 : (0 : ℝ) < v ^ 2 := by positivity
  have hC : (0 : ℝ) < m * v ^ 2 / 2 := by positivity
  have hdiff2 : bodyKineticEnergy m (wallReboundVelocity e v) - bodyKineticEnergy m v =
      (e ^ 2 - 1) * (m * v ^ 2 / 2) := by linear_combination hdiff
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have h0 : (e ^ 2 - 1) * (m * v ^ 2 / 2) < 0 := by linarith [hdiff2, h]
    have hneg : e ^ 2 - 1 < 0 := by
      by_contra hc
      push Not at hc
      have hge : (0 : ℝ) ≤ (e ^ 2 - 1) * (m * v ^ 2 / 2) :=
        mul_nonneg hc (le_of_lt hC)
      linarith
    by_contra hc
    push Not at hc
    have h1e : (0 : ℝ) ≤ e - 1 := by linarith
    have h1e' : (0 : ℝ) ≤ e + 1 := by linarith
    have h1 : (0 : ℝ) ≤ (e - 1) * (e + 1) := mul_nonneg h1e h1e'
    linarith
  · intro h
    have h1e : (0 : ℝ) < 1 - e := by linarith
    have h1e' : (0 : ℝ) < 1 + e := by linarith
    have hprod : (0 : ℝ) < (1 - e) * (1 + e) := mul_pos h1e h1e'
    have he2 : e ^ 2 < 1 := by linarith [hprod]
    have hnn : e ^ 2 - 1 < 0 := by linarith
    have h0 : (e ^ 2 - 1) * (m * v ^ 2 / 2) < 0 :=
      mul_neg_of_neg_of_pos hnn hC
    linarith [hdiff2]
  · intro h
    have h0 : (e ^ 2 - 1) * (m * v ^ 2 / 2) = 0 := by linarith [hdiff2, h]
    have hC0 : m * v ^ 2 / 2 ≠ 0 := ne_of_gt hC
    rcases mul_eq_zero.mp h0 with hleft | hright
    · have hfac : (e - 1) * (e + 1) = 0 := by linear_combination hleft
      have hpos1 : (0 : ℝ) < e + 1 := by linarith
      have hne : e + 1 ≠ 0 := ne_of_gt hpos1
      rcases mul_eq_zero.mp hfac with h1 | h2
      · linarith [h1]
      · exact absurd h2 hne
    · exact absurd hright hC0
  · intro h
    have h0 : (e ^ 2 - 1) * (m * v ^ 2 / 2) = 0 := by
      rw [h]
      norm_num
    linarith [hdiff2]
  · intro h
    have h0 : (0 : ℝ) < (e ^ 2 - 1) * (m * v ^ 2 / 2) := by linarith [hdiff2, h]
    have hpos : (0 : ℝ) < e ^ 2 - 1 := by
      by_contra hc
      push Not at hc
      have hle : (e ^ 2 - 1) * (m * v ^ 2 / 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (le_of_lt hC)
      linarith
    by_contra hc
    push Not at hc
    have h1e : (0 : ℝ) ≤ 1 - e := by linarith
    have h1e' : (0 : ℝ) ≤ 1 + e := by linarith
    have h1 : (0 : ℝ) ≤ (1 - e) * (1 + e) := mul_nonneg h1e h1e'
    linarith
  · intro h
    have h1e : (0 : ℝ) < e - 1 := by linarith
    have h1e' : (0 : ℝ) < e + 1 := by linarith
    have hprod : (0 : ℝ) < (e - 1) * (e + 1) := mul_pos h1e h1e'
    have he2 : (0 : ℝ) < e ^ 2 - 1 := by linarith [hprod]
    have h0 : (0 : ℝ) < (e ^ 2 - 1) * (m * v ^ 2 / 2) := mul_pos he2 hC
    linarith [hdiff2]

/-! ## F. The wall impulse and the continuous phase -/

/-- After the event the body follows the actual constant-force trajectory started at `v⁺` under
the external force `F`; at time `t` after the event its momentum is the incoming momentum plus the
wall impulse plus the impulse `t F` of the force. -/
lemma rebound_then_flight_momentum {m : ℝ} (hm : 0 < m) (e v F t : ℝ) :
    m * constForceVelocity m (wallReboundVelocity e v) F t = m * v + wallImpulse m e v + t * F := by
  have hm' : m ≠ 0 := ne_of_gt hm
  unfold constForceVelocity wallImpulse wallReboundVelocity
  simp only [smul_eq_mul]
  field_simp
  ring

section BouncingBall

open Robotics.Hybrid

/-! ## G. Ballistic arcs and the bounce sequence -/

/-- Take-off speed of arc `n`: `u₀` for the first arc, then the rebound velocity of the fixed-wall
event applied to the arrival velocity `-u` of the previous arc. -/
noncomputable def bounceSpeed (e u₀ : ℝ) : ℕ → ℝ
  | 0 => u₀
  | n + 1 => wallReboundVelocity e (-bounceSpeed e u₀ n)

/-- Flight duration `T_n = 2 u_n / g` of arc `n`. -/
noncomputable def flightDuration (g e u₀ : ℝ) (n : ℕ) : ℝ :=
  2 * bounceSpeed e u₀ n / g

/-- Accumulation time `t_∞ = 2 u₀ / (g (1 - e))`. -/
noncomputable def zenoTime (g e u₀ : ℝ) : ℝ :=
  2 * u₀ / (g * (1 - e))

/-- Take-off speeds of the bounce sequence: `u_n = e ^ n u₀`. -/
lemma bounceSpeed_eq (e u₀ : ℝ) (n : ℕ) : bounceSpeed e u₀ n = e ^ n * u₀ := by
  induction n with
  | zero => simp [bounceSpeed]
  | succ n ih => simp [bounceSpeed, wallReboundVelocity, ih, pow_succ]; ring

/-- Arc `n` is active when its take-off speed is positive, so that the ball leaves the floor; an
arc with take-off speed `0` is no flight, and the ball rests on the floor. The contacts of the
bounce sequence are the ends of its active arcs: an index whose arc is not active is rest, not a
further impact. -/
def IsActiveArc (e u₀ : ℝ) (n : ℕ) : Prop :=
  0 < bounceSpeed e u₀ n

/-- For `e > 0` and `u₀ > 0` every arc is active: the take-off speeds `e ^ n u₀` stay positive,
so the bounces never stop. -/
lemma isActiveArc_of_pos {e u₀ : ℝ} (he : 0 < e) (hu : 0 < u₀) (n : ℕ) : IsActiveArc e u₀ n := by
  rw [IsActiveArc, bounceSpeed_eq]
  positivity

/-- **Arc and event.** For `m > 0` and `g > 0`, an active arc `n` (`IsActiveArc`: take-off speed
`u_n > 0`), the constant-force trajectory from the floor with take-off speed `u_n` under the weight
`-(m g)`, has the positive duration `T_n`, is back on the floor at `T_n`, stays above it on
`(0, T_n)` and arrives with velocity `-u_n`; the fixed-wall event applied to that arrival velocity
gives the take-off speed `u_(n+1)` of the next arc. For `e > 0` and `u₀ > 0` every arc is active
(`isActiveArc_of_pos`); for `e = 0` only the first one is (`inelastic_stops`). -/
lemma bounce_arc {m g e u₀ : ℝ} {n : ℕ} (hm : 0 < m) (hg : 0 < g) (hact : IsActiveArc e u₀ n) :
    0 < flightDuration g e u₀ n ∧
      constForcePosition m 0 (bounceSpeed e u₀ n) (-(m * g)) (flightDuration g e u₀ n) = 0 ∧
      (∀ t ∈ Set.Ioo 0 (flightDuration g e u₀ n),
        0 < constForcePosition m 0 (bounceSpeed e u₀ n) (-(m * g)) t) ∧
      constForceVelocity m (bounceSpeed e u₀ n) (-(m * g)) (flightDuration g e u₀ n) =
        -bounceSpeed e u₀ n ∧
      wallReboundVelocity e
          (constForceVelocity m (bounceSpeed e u₀ n) (-(m * g)) (flightDuration g e u₀ n)) =
        bounceSpeed e u₀ (n + 1) := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hg' : g ≠ 0 := ne_of_gt hg
  set u : ℝ := bounceSpeed e u₀ n with hu_def
  have hu_pos : 0 < u := hact
  have hT : flightDuration g e u₀ n = 2 * u / g := rfl
  have htraj : ∀ t : ℝ, constForcePosition m 0 u (-(m * g)) t = t * (u - g * t / 2) := by
    intro t
    simp only [constForcePosition, smul_eq_mul, zero_add]
    field_simp
    ring
  have hvel : constForceVelocity m u (-(m * g)) (flightDuration g e u₀ n) = -u := by
    simp only [constForceVelocity, smul_eq_mul, hT]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, hvel, ?_⟩
  · rw [hT]
    exact div_pos (by linarith) hg
  · rw [htraj, hT]
    field_simp
    ring
  · intro t ht
    rw [htraj]
    have h2 : t < 2 * u / g := by simpa [hT] using ht.2
    have hgt : g * t < 2 * u := by
      rw [mul_comm g t]
      exact (lt_div_iff₀ hg).mp h2
    have h3 : 0 < u - g * t / 2 := by linarith
    exact mul_pos ht.1 h3
  · rw [hvel, hu_def, bounceSpeed]

/-- Flight durations proportional to `e ^ n`: `T_n = (2 u₀ / g) e ^ n`. -/
lemma flightDuration_eq (g e u₀ : ℝ) (n : ℕ) : flightDuration g e u₀ n = 2 * u₀ / g * e ^ n := by
  simp [flightDuration, bounceSpeed_eq]
  ring

/-! ## H. The finite sum and Zeno accumulation -/

/-- **Finite sum.** For `0 < e < 1` the flight durations sum to `t_∞ = 2 u₀ / (g (1 - e))`. The
identity holds for every `g` and `u₀` (at `g = 0` both sides are `0` by Lean's division); it is the
accumulation time of the bounces for `g > 0` and `u₀ > 0` (`zeno_accumulation`). -/
lemma hasSum_flightDuration {g e u₀ : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    HasSum (flightDuration g e u₀) (zenoTime g e u₀) := by
  have hgeom : HasSum (fun n => e ^ n) ((1 - e)⁻¹) :=
    hasSum_geometric_of_lt_one he0.le he1
  have hmul := hgeom.mul_left (2 * u₀ / g)
  have hfun : ∀ n, flightDuration g e u₀ n = 2 * u₀ / g * e ^ n :=
    flightDuration_eq g e u₀
  have hval : 2 * u₀ / g * (1 - e)⁻¹ = zenoTime g e u₀ := by
    simp only [zenoTime, div_eq_mul_inv, mul_inv]
    ring
  rw [hval] at hmul
  exact hmul.congr_fun hfun

/-- **Zeno accumulation.** For `g > 0`, `u₀ > 0` and `0 < e < 1` the contact times
`dwellElapsed T N` increase strictly, stay below `t_∞` and tend to it, while the take-off speeds
tend to `0`: infinitely many impacts occur before the finite time `t_∞`. -/
lemma zeno_accumulation {g e u₀ : ℝ} (hg : 0 < g) (hu : 0 < u₀) (he0 : 0 < e) (he1 : e < 1) :
    StrictMono (dwellElapsed (flightDuration g e u₀)) ∧
      (∀ N, dwellElapsed (flightDuration g e u₀) N < zenoTime g e u₀) ∧
      Filter.Tendsto (dwellElapsed (flightDuration g e u₀)) Filter.atTop
        (nhds (zenoTime g e u₀)) ∧
      Filter.Tendsto (bounceSpeed e u₀) Filter.atTop (nhds 0) := by
  have hpos : ∀ n, 0 < flightDuration g e u₀ n := by
    intro n
    rw [flightDuration_eq]
    exact mul_pos (div_pos (mul_pos (by norm_num) hu) hg) (pow_pos he0 n)
  have hnonneg : ∀ n, 0 ≤ flightDuration g e u₀ n := fun n => (hpos n).le
  have hsum : HasSum (flightDuration g e u₀) (zenoTime g e u₀) :=
    hasSum_flightDuration he0 he1
  have htsum : ∑' n, flightDuration g e u₀ n = zenoTime g e u₀ := hsum.tsum_eq
  have hstep : ∀ n, dwellElapsed (flightDuration g e u₀) n <
      dwellElapsed (flightDuration g e u₀) (n + 1) := by
    intro n
    simp only [dwellElapsed, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (hpos n)
  refine ⟨strictMono_nat_of_lt_succ hstep, ?_, hsum.tendsto_sum_nat, ?_⟩
  · intro N
    have h2 : dwellElapsed (flightDuration g e u₀) (N + 1) ≤
        ∑' n, flightDuration g e u₀ n := by
      have hle := hsum.summable.sum_le_tsum (Finset.range (N + 1))
        (fun i _ => hnonneg i)
      simpa [dwellElapsed] using hle
    rw [htsum] at h2
    exact lt_of_lt_of_le (hstep N) h2
  · have hpow : Filter.Tendsto (fun n => e ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one he0.le he1
    have hmul := hpow.mul_const u₀
    have hfun : bounceSpeed e u₀ = fun n => e ^ n * u₀ :=
      funext (bounceSpeed_eq e u₀)
    rw [hfun]
    simpa using hmul

/-- The flight durations are summable exactly when `e < 1` (for `g > 0`, `u₀ > 0`, `e ≥ 0`). -/
lemma summable_flightDuration_iff {g e u₀ : ℝ} (hg : 0 < g) (hu : 0 < u₀) (he : 0 ≤ e) :
    Summable (flightDuration g e u₀) ↔ e < 1 := by
  have hc : 0 < 2 * u₀ / g := div_pos (mul_pos (by norm_num) hu) hg
  constructor
  · intro hsum
    by_contra hcon
    have hge : 1 ≤ e := not_lt.mp hcon
    have htend : Filter.Tendsto (flightDuration g e u₀) Filter.atTop (nhds 0) :=
      hsum.tendsto_atTop_zero
    have hge1 : ∀ n, 2 * u₀ / g ≤ flightDuration g e u₀ n := by
      intro n
      rw [flightDuration_eq]
      calc 2 * u₀ / g = 2 * u₀ / g * 1 := by ring
        _ ≤ 2 * u₀ / g * e ^ n :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hge) hc.le
    have hle : 2 * u₀ / g ≤ 0 :=
      ge_of_tendsto htend (Filter.Eventually.of_forall hge1)
    linarith
  · intro he1
    have hgeom : Summable (fun n => e ^ n) := summable_geometric_of_lt_one he he1
    have hmul := hgeom.mul_left (2 * u₀ / g)
    exact (summable_congr (flightDuration_eq g e u₀)).mpr hmul

/-! ## I. No dwell-time lower bound for the Zeno family -/

/-- The Zeno family has no positive dwell-time lower bound: for `g > 0`, `u₀ > 0` and
`0 < e < 1`, no `δ > 0` bounds every flight duration from below. -/
lemma zeno_no_dwell {g e u₀ : ℝ} (hg : 0 < g) (hu : 0 < u₀) (he0 : 0 < e) (he1 : e < 1) :
    ¬ ∃ δ > 0, ∀ k, δ ≤ flightDuration g e u₀ k := by
  rintro ⟨δ, hδ, hd⟩
  have hsum : Summable (flightDuration g e u₀) :=
    (summable_flightDuration_iff hg hu he0.le).mpr he1
  have htend : Filter.Tendsto (flightDuration g e u₀) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hle : δ ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hd)
  linarith

/-! ## J. The boundary cases `e = 1` and `e = 0` -/

/-- `e = 1` does not accumulate in finite time: for `g > 0` and `u₀ > 0` the durations are not
summable, and only finitely many impacts occur up to any horizon `H` (dwell time `2 u₀ / g`). -/
lemma elastic_events_finite {g u₀ : ℝ} (hg : 0 < g) (hu : 0 < u₀) :
    ¬ Summable (flightDuration g 1 u₀) ∧
      ∀ H, {n : ℕ | dwellElapsed (flightDuration g 1 u₀) n ≤ H}.Finite := by
  have hc : 0 < 2 * u₀ / g := div_pos (mul_pos (by norm_num) hu) hg
  have hconst : ∀ n, flightDuration g 1 u₀ n = 2 * u₀ / g := by
    intro n
    rw [flightDuration_eq]
    simp
  refine ⟨?_, ?_⟩
  · intro hsum
    have htend : Filter.Tendsto (flightDuration g 1 u₀) Filter.atTop (nhds 0) :=
      hsum.tendsto_atTop_zero
    have hfun : flightDuration g 1 u₀ = fun _ => 2 * u₀ / g := funext hconst
    rw [hfun] at htend
    have hzero : 2 * u₀ / g = 0 := tendsto_const_nhds_iff.mp htend
    linarith
  · intro H
    exact (Robotics.Hybrid.events_finite_of_dwell hc (fun k => (hconst k).ge) H).1

/-- **Termination for `e = 0`.** For `g > 0` and `u₀ > 0` the first arc, with take-off speed
`u₀`, is the only active arc, and it ends at the positive time `2 u₀ / g`, the first and only
impact; as an active arc it is a ballistic flight that lands there with velocity `-u₀`
(`bounce_arc`). The ball then rests on the floor: every later take-off speed and flight duration
is `0`, so the elapsed time stays at `2 u₀ / g`; the later indices are rest, not further
impacts. -/
lemma inelastic_stops {g u₀ : ℝ} (hg : 0 < g) (hu : 0 < u₀) :
    {n : ℕ | IsActiveArc 0 u₀ n} = {0} ∧ 0 < dwellElapsed (flightDuration g 0 u₀) 1 ∧
      ∀ n, bounceSpeed 0 u₀ (n + 1) = 0 ∧ flightDuration g 0 u₀ (n + 1) = 0 ∧
        dwellElapsed (flightDuration g 0 u₀) (n + 1) = 2 * u₀ / g := by
  have h0 : ∀ k, bounceSpeed 0 u₀ (k + 1) = 0 := by
    intro k
    simp [bounceSpeed, wallReboundVelocity]
  have h1 : ∀ k, flightDuration g 0 u₀ (k + 1) = 0 := by
    intro k
    simp [flightDuration, bounceSpeed, wallReboundVelocity]
  have hrest : ∀ n, dwellElapsed (flightDuration g 0 u₀) (n + 1) = 2 * u₀ / g := by
    intro n
    simp only [dwellElapsed, Finset.sum_range_succ']
    have hsum0 : ∑ k ∈ Finset.range n, flightDuration g 0 u₀ (k + 1) = 0 :=
      Finset.sum_eq_zero (fun k _ => h1 k)
    rw [hsum0, zero_add]
    simp [flightDuration, bounceSpeed]
  refine ⟨?_, ?_, fun n => ⟨h0 n, h1 n, hrest n⟩⟩
  · ext n
    cases n with
    | zero => simp [IsActiveArc, bounceSpeed, hu]
    | succ k => simp [IsActiveArc, h0 k]
  · rw [hrest 0]
    positivity

end BouncingBall

end PhyslibExt.Mechanics.ImpactAndDeployment
