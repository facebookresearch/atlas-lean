/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.HenryLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Interphase mass transfer with a Henry equilibrium

Signed interphase molar flux `J = k * a * (H * p - c)` per unit area, where
`H * p` is the equilibrium liquid concentration under the Henry convention
`c = H * p` used in `PhyslibExt.EarthScience.HenryLaw`. Positive flux is
absorption into the liquid; negative flux is desorption. The reciprocal
volatility convention `c* = p / H_pc` is related by `H = 1 / H_pc`, as in
`EarthScience.henry_conversion_reciprocal`.
-/

@[expose] public section

namespace Engineering.Process.MassTransfer

/-- Signed interphase molar flux `J = k * a * (c* - c)` per unit area, with
equilibrium concentration `c* = H * p` under the declared Henry convention
`c = H * p` (`H` is the concentration/pressure constant `H_cp`). Positive
`J` is absorption into the liquid; negative `J` is desorption. `k * a` is
the volumetric mass-transfer coefficient factor, `p` an absolute partial
pressure, `c` the liquid concentration. -/
def interphaseFlux (k a H p c : ℝ) : ℝ :=
  k * a * (H * p - c)

/-- The flux is the coefficient times the driving force `H * p - c`. -/
lemma interphaseFlux_apply (k a H p c : ℝ) :
    interphaseFlux k a H p c = k * a * (H * p - c) :=
  rfl

/-- Absorption: below equilibrium (`c < H * p`), the flux is positive for
positive `k` and `a`. -/
lemma interphaseFlux_pos {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a)
    (h : c < H * p) : 0 < interphaseFlux k a H p c := by
  unfold interphaseFlux
  exact mul_pos (mul_pos hk ha) (sub_pos.mpr h)

/-- Desorption: above equilibrium (`H * p < c`), the flux is negative for
positive `k` and `a`; it is not a nonnegative source. -/
lemma interphaseFlux_neg {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a)
    (h : H * p < c) : interphaseFlux k a H p c < 0 := by
  unfold interphaseFlux
  exact mul_neg_of_pos_of_neg (mul_pos hk ha) (sub_neg.mpr h)

/-- Zero driving force: for positive `k` and `a`, the flux vanishes exactly
at equilibrium `c = H * p`. -/
lemma interphaseFlux_eq_zero_iff {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a) :
    interphaseFlux k a H p c = 0 ↔ c = H * p := by
  unfold interphaseFlux
  have hka : k * a ≠ 0 := ne_of_gt (mul_pos hk ha)
  constructor
  · intro h
    have h1 : H * p - c = 0 := by
      rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd h2 hka
      · exact h2
    exact (sub_eq_zero.mp h1).symm
  · intro h
    rw [h, sub_self, mul_zero]

/-- Doubling the partial pressure doubles the equilibrium concentration in
the flux: the driving force at `2 * p` is `2 * (H * p) - c`. -/
lemma interphaseFlux_pressure_double (k a H p c : ℝ) :
    interphaseFlux k a H (2 * p) c = k * a * (2 * (H * p) - c) := by
  have hinner : H * (2 * p) = 2 * (H * p) := by ring
  unfold interphaseFlux
  rw [hinner]

/-- Pressure-form conversion: with the volatility convention
`c* = p / H_pc` where `H = 1 / H_pc` (the reciprocal convention of
`EarthScience.henry_conversion_reciprocal`), the flux is
`k * a * (p / H_pc - c)`. -/
lemma interphaseFlux_volatility_form {k a H H_pc p c : ℝ} (hHpc : H_pc ≠ 0)
    (hH : H = 1 / H_pc) :
    interphaseFlux k a H p c = k * a * (p / H_pc - c) := by
  have hinner : H * p = p / H_pc := by
    rw [hH]
    field_simp
  unfold interphaseFlux
  rw [hinner]

end Engineering.Process.MassTransfer
