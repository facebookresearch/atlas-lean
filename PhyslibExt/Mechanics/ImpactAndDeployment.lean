/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.PowerPorts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Instantaneous impact events

Two bodies of masses `m₁, m₂ > 0` move on one line and collide instantaneously, or one body of
mass `m > 0` meets a stationary wall. Velocities are components along the line of the impact:
`v₁, v₂` (or `v⁻`) just before the event and `u₁, u₂` (or `v⁺`) just after it.

## i. Overview

The event map solves momentum conservation `m₁ u₁ + m₂ u₂ = m₁ v₁ + m₂ v₂` together with
Newton's restitution law `u₂ - u₁ = -e (v₂ - v₁)` for a coefficient of restitution `e ∈ [0, 1]`,
and the solution is unique. The kinetic energy drops by
`(1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`: no loss for `e = 1`, and a gain for `e > 1`, which is
therefore outside the model.

During the event body 1 receives the impulse `J = -(1 + e) μ (v₁ - v₂)`, with the reduced mass
`μ = m₁ m₂ / (m₁ + m₂)`, and body 2 receives `-J`; each momentum jump is the impulse received,
the event form of the impulse identity of `PhyslibExt.Mechanics.PowerPorts`. After the event each
body follows the actual constant-force trajectory of that module started at its post-impact
velocity: the total momentum is the pre-impact total plus the external impulse, and in free
flight the kinetic energy stays at its pre-impact value minus the event loss.

At a fixed wall the normal axis points from the wall into the body's side, so an incoming body has
`v⁻ < 0`, and the event maps `v⁻` to `v⁺ = -e v⁻`: the body leaves the wall, or rests on it when
`e = 0`. The wall delivers the impulse `J = m (v⁺ - v⁻) = -(1 + e) m v⁻ > 0`, the body's momentum
jumps by exactly `J`, and so the body alone does not conserve momentum. Its kinetic energy changes
by `-(1 - e²) m v⁻² / 2`: a strict loss exactly when `e < 1`, none exactly when `e = 1`, and a gain
exactly when `e > 1`. After the event the body follows the same constant-force trajectory from
`v⁺`, and its momentum at time `t` is `m v⁻ + J + t F`.

Model inputs: a one-dimensional isolated two-body instantaneous impact, with no external impulse
during the event; `e` is the coefficient of restitution, and the event algebra holds for every
real `e`, only the sign of the energy loss using the range `[0, 1]`. Contact forces during the
impact, oblique or rotational impact, multiple simultaneous contacts, event detection, Zeno
behavior, and empirical adequacy or system safety are not treated. The fixed wall is an
external-impulse model with one normal direction, not a limit of the finite-mass collision.

## ii. Key results

- `impact_solve_iff`: the event map is the unique solution of momentum conservation and the
  restitution law.
- `impact_energy_loss`: the kinetic-energy loss `(1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`.
- `impact_energy_le`, `impact_energy_eq_of_elastic`, `impact_energy_lt_of_one_lt`: no gain for
  `e ∈ [0, 1]`, conservation for `e = 1`, a gain for `e > 1`.
- `impact_impulse`: equal and opposite event impulses.
- `impact_then_flight_momentum`, `impact_then_free_flight_energy`: momentum and kinetic energy
  across the event and the following constant-force phase.
- `wallReboundVelocity_nonneg`, `wallImpulse_eq`, `wallImpulse_pos`, `body_momentum_ne`: the
  fixed-wall rebound, its outward impulse and the body's momentum change.
- `wall_energy_change`, `wall_energy_cases`: the body's exact kinetic-energy change and its sign
  for each range of the restitution coefficient.
- `rebound_then_flight_momentum`: the wall impulse and the impulse of the following
  constant-force phase in one momentum balance.

## iii. Table of contents

- A. The two-body event map
- B. Kinetic energy across the event
- C. Event ports and the continuous phase
- D. The fixed-wall event
- E. Kinetic energy of the body
- F. The wall impulse and the continuous phase

## iv. References

- F. P. Beer and E. R. Johnston Jr., *Vector Mechanics for Engineers: Dynamics*, chapter 13
  (direct central impact, coefficient of restitution).
- R. C. Hibbeler, *Engineering Mechanics: Dynamics*, 14th edition, chapter 15 (impact,
  coefficient of restitution).
- W. J. Stronge, *Impact Mechanics*, chapter 1 (Newton's coefficient of restitution and the
  energy loss of a direct collision).
- `PhyslibExt.Mechanics.PowerPorts`: the constant-force trajectory and the impulse identity.
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

/-- An incoming body leaves the wall or rests on it: `v⁺ ≥ 0`, with `v⁺ > 0` exactly when
`e > 0`. -/
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

/-- For an incoming body the wall impulse points out of the wall. -/
lemma wallImpulse_pos {m e v : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hv : v < 0) :
    0 < wallImpulse m e v := by
  rw [wallImpulse_eq]
  have h1 : (0 : ℝ) < (1 + e) * m := mul_pos (by linarith) hm
  have h2 : (1 + e) * m * v < 0 := mul_neg_of_pos_of_neg h1 hv
  linarith

/-- The body alone does not conserve momentum: for `v⁻ ≠ 0` its momentum changes. -/
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

end PhyslibExt.Mechanics.ImpactAndDeployment
