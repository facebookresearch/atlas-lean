/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Typical-section static divergence

## i. Overview

A rigid airfoil section on a torsional spring of stiffness `K` about its elastic axis,
in a quasi-steady linear aerodynamic moment model. The twist `θ` (rad) and the rigid
angle of attack `α₀` (rad) are nose-up positive. The lift is `q * S * CLα * (α₀ + θ)`
with dynamic pressure `q`, reference area `S` and lift-curve slope `CLα` (per rad).
The offset `e` is the distance from the elastic axis forward to the aerodynamic centre,
positive when the aerodynamic centre lies ahead of the elastic axis, so the aerodynamic
moment about the elastic axis, nose-up positive, is `q * S * e * CLα * (α₀ + θ)`.

The static moment balance about the elastic axis is `restoringMoment = 0`, where the net
restoring moment is the elastic moment `K * θ` minus the aerodynamic moment. It is affine
in `θ` with slope `K - q * (S * e * CLα)`, the effective stiffness. For `0 < K` and a
positive aerodynamic factor `0 < S * e * CLα`:

* the effective stiffness vanishes exactly at the divergence dynamic pressure
  `qD = K / (S * e * CLα)`, which is positive;
* it is positive exactly below `qD`, and below `qD` the only twist balancing the moment
  with zero rigid angle is `θ = 0`;
* at `qD` every twist, in particular a nonzero one, balances the moment with zero rigid
  angle: a neutral displacement.

The sign of `e * CLα` matters. For a nonpositive factor `S * e * CLα ≤ 0` the effective
stiffness stays positive at every nonnegative dynamic pressure and the division formula
gives no positive pressure. For a zero factor the formula `K / 0` evaluates to `0`, which
is not a pressure at which the stiffness vanishes.

Model inputs: the quasi-steady linear moment law and the linear spring. Non-goals:
unsteady aerodynamics, flutter, a three-dimensional wing, empirical adequacy and any
vehicle or system safety claim.

## ii. Key results

- `Elasticity.AeroelasticModels.restoringMoment_eq`,
  `Elasticity.AeroelasticModels.hasDerivAt_restoringMoment`: the net restoring moment is
  affine in the twist, with slope the effective stiffness.
- `Elasticity.AeroelasticModels.divergencePressure_pos`,
  `Elasticity.AeroelasticModels.effectiveStiffness_eq_zero_iff`,
  `Elasticity.AeroelasticModels.effectiveStiffness_pos_iff`: the divergence pressure is
  positive, the stiffness vanishes exactly there and is positive exactly below it.
- `Elasticity.AeroelasticModels.eq_zero_of_restoringMoment_eq_zero`,
  `Elasticity.AeroelasticModels.restoringMoment_divergencePressure`,
  `Elasticity.AeroelasticModels.exists_neutral_displacement`: no neutral twist below the
  divergence pressure, every twist neutral at it.
- `Elasticity.AeroelasticModels.coupling_nonpos`,
  `Elasticity.AeroelasticModels.coupling_zero`: the nonpositive and zero aerodynamic factor.

## iii. Table of contents

- A. Moment model
- B. Effective stiffness
- C. Divergence pressure
- D. Nonpositive and zero aerodynamic factor

## iv. References

- R. L. Bisplinghoff, H. Ashley and R. L. Halfman, *Aeroelasticity*, 1955 (typical section).
- D. H. Hodges and G. A. Pierce, *Introduction to Structural Dynamics and Aeroelasticity*,
  2nd edition, 2011 (static divergence of the typical section).
-/

@[expose] public section

namespace Elasticity.AeroelasticModels

/-! ## A. Moment model -/

/-- Aerodynamic moment about the elastic axis, nose-up positive:
`q * S * e * CLα * (α₀ + θ)`. -/
def aeroMoment (q S e CLα α₀ θ : ℝ) : ℝ :=
  q * S * e * CLα * (α₀ + θ)

/-- Net restoring moment about the elastic axis: the elastic moment `K * θ` minus the
aerodynamic moment. Static equilibrium is `restoringMoment K q S e CLα α₀ θ = 0`. -/
def restoringMoment (K q S e CLα α₀ θ : ℝ) : ℝ :=
  K * θ - aeroMoment q S e CLα α₀ θ

/-- Effective torsional stiffness `K - q * (S * e * CLα)`. -/
def effectiveStiffness (K q S e CLα : ℝ) : ℝ :=
  K - q * (S * e * CLα)

/-- Divergence dynamic pressure `K / (S * e * CLα)`. For a zero aerodynamic factor this
division evaluates to `0`; it is meaningful only for a nonzero factor. -/
noncomputable def divergencePressure (K S e CLα : ℝ) : ℝ :=
  K / (S * e * CLα)

/-! ## B. Effective stiffness -/

/-- The net restoring moment is affine in the twist, with slope the effective
stiffness. -/
lemma restoringMoment_eq (K q S e CLα α₀ θ : ℝ) :
    restoringMoment K q S e CLα α₀ θ =
      effectiveStiffness K q S e CLα * θ - q * (S * e * CLα) * α₀ := by
  unfold restoringMoment aeroMoment effectiveStiffness
  ring

/-- The effective stiffness is the derivative of the net restoring moment with respect
to the twist. -/
lemma hasDerivAt_restoringMoment (K q S e CLα α₀ θ : ℝ) :
    HasDerivAt (restoringMoment K q S e CLα α₀) (effectiveStiffness K q S e CLα) θ := by
  rw [hasDerivAt_iff_isLittleO]
  have h : (fun x' : ℝ => restoringMoment K q S e CLα α₀ x' -
      restoringMoment K q S e CLα α₀ θ - (x' - θ) • effectiveStiffness K q S e CLα) =
      fun _ => 0 := by
    funext x'
    unfold restoringMoment aeroMoment effectiveStiffness
    simp only [smul_eq_mul]
    ring
  rw [h]
  exact Asymptotics.isLittleO_zero _ _

/-! ## C. Divergence pressure -/

/-- For positive stiffness and positive aerodynamic factor the divergence pressure is
positive. -/
lemma divergencePressure_pos {K S e CLα : ℝ} (hK : 0 < K) (hc : 0 < S * e * CLα) :
    0 < divergencePressure K S e CLα := by
  unfold divergencePressure
  exact div_pos hK hc

/-- For a positive aerodynamic factor the effective stiffness vanishes exactly at the
divergence pressure. -/
lemma effectiveStiffness_eq_zero_iff {K q S e CLα : ℝ} (hc : 0 < S * e * CLα) :
    effectiveStiffness K q S e CLα = 0 ↔ q = divergencePressure K S e CLα := by
  have hc' : S * e * CLα ≠ 0 := ne_of_gt hc
  unfold effectiveStiffness divergencePressure
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [eq_div_iff hc']
    linarith
  · intro h
    rw [eq_div_iff hc'] at h
    linarith

/-- For a positive aerodynamic factor the effective stiffness is positive exactly below
the divergence pressure. -/
lemma effectiveStiffness_pos_iff {K q S e CLα : ℝ} (hc : 0 < S * e * CLα) :
    0 < effectiveStiffness K q S e CLα ↔ q < divergencePressure K S e CLα := by
  unfold effectiveStiffness divergencePressure
  rw [sub_pos, lt_div_iff₀ hc]

/-- Below the divergence pressure the only twist balancing the moment with zero rigid
angle is `θ = 0`. -/
lemma eq_zero_of_restoringMoment_eq_zero {K q S e CLα θ : ℝ} (hc : 0 < S * e * CLα)
    (hq : q < divergencePressure K S e CLα) (hθ : restoringMoment K q S e CLα 0 θ = 0) :
    θ = 0 := by
  have hpos : 0 < effectiveStiffness K q S e CLα :=
    (effectiveStiffness_pos_iff hc).mpr hq
  have hne : effectiveStiffness K q S e CLα ≠ 0 := ne_of_gt hpos
  have heq := restoringMoment_eq K q S e CLα 0 θ
  rw [hθ] at heq
  simp only [mul_zero, sub_zero] at heq
  have heq' : effectiveStiffness K q S e CLα * θ = 0 := heq.symm
  exact (mul_eq_zero.mp heq').resolve_left hne

/-- At the divergence pressure every twist balances the moment with zero rigid angle. -/
lemma restoringMoment_divergencePressure {K S e CLα : ℝ} (hc : S * e * CLα ≠ 0)
    (θ : ℝ) : restoringMoment K (divergencePressure K S e CLα) S e CLα 0 θ = 0 := by
  have heq := restoringMoment_eq K (divergencePressure K S e CLα) S e CLα 0 θ
  have hK : effectiveStiffness K (divergencePressure K S e CLα) S e CLα = 0 := by
    unfold effectiveStiffness divergencePressure
    rw [div_mul_cancel₀ _ hc, sub_self]
  rw [heq, hK]
  simp

/-- Neutral displacement: the divergence pressure is positive and a nonzero twist
balances the moment there with zero rigid angle. -/
lemma exists_neutral_displacement {K S e CLα : ℝ} (hK : 0 < K) (hc : 0 < S * e * CLα) :
    0 < divergencePressure K S e CLα ∧
      ∃ θ : ℝ, θ ≠ 0 ∧ restoringMoment K (divergencePressure K S e CLα) S e CLα 0 θ = 0 := by
  exact ⟨divergencePressure_pos hK hc, 1, one_ne_zero,
    restoringMoment_divergencePressure (ne_of_gt hc) 1⟩

/-! ## D. Nonpositive and zero aerodynamic factor -/

/-- Nonpositive factor branch: the division formula gives no positive pressure, and the
effective stiffness stays positive at every nonnegative dynamic pressure. -/
lemma coupling_nonpos {K S e CLα : ℝ} (hK : 0 < K) (hc : S * e * CLα ≤ 0) :
    divergencePressure K S e CLα ≤ 0 ∧
      ∀ q : ℝ, 0 ≤ q → 0 < effectiveStiffness K q S e CLα := by
  constructor
  · unfold divergencePressure
    exact div_nonpos_of_nonneg_of_nonpos (le_of_lt hK) hc
  · intro q hq
    unfold effectiveStiffness
    have hqc : q * (S * e * CLα) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq hc
    linarith

/-- Zero factor: the division formula evaluates to `0` and no dynamic pressure makes
the effective stiffness vanish. -/
lemma coupling_zero {K S e CLα : ℝ} (hK : 0 < K) (hc : S * e * CLα = 0) :
    divergencePressure K S e CLα = 0 ∧ ¬ ∃ q : ℝ, effectiveStiffness K q S e CLα = 0 := by
  constructor
  · unfold divergencePressure
    rw [hc, div_zero]
  · rintro ⟨q, hq⟩
    unfold effectiveStiffness at hq
    rw [hc, mul_zero, sub_zero] at hq
    exact ne_of_gt hK hq

end Elasticity.AeroelasticModels

end
