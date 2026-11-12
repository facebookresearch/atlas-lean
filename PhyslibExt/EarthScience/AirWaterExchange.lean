/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Air-water exchange with a conserved inventory

Closed isothermal two-compartment system: gas amount `ng` and dissolved
amount `nw` exchange through the flux `J = k * A * (H * p - c)` with
`p = ng * R * T / Vg` and `c = nw / Vw`, satisfying `ng' = -J` and
`nw' = J`. The total inventory `ng + nw` is conserved, and the
disequilibrium `d = H * p - c` decays exponentially at rate
`k * A * (H * R * T / Vg + 1 / Vw)`.

## i. Overview

Conservation is the cancellation of `+J` against `-J` in the derivative
of the total. The disequilibrium obeys a linear decay equation because
differentiating `H * p - c` pulls out one factor of the flux coefficient
from each compartment, and a function satisfying `d' = -rate * d`
everywhere decays as `d(t) = d(0) * exp (-rate * t)`. This is a closed
isothermal ideal-gas/Henry model with constant geometry; an external gas
source would add to the total budget rather than vanish.

## ii. Key results

- `EarthScience.air_water_total_conserved`: total inventory derivative `0`.
- `EarthScience.air_water_difference_ode`: disequilibrium decay equation.
- `EarthScience.exp_decay_of_linear_ode`: exponential decay from the
  linear ODE.

## iii. Table of contents

- A. Total inventory conservation
- B. Disequilibrium decay equation
- C. Exponential decay

## iv. References

- `HasDerivAt` API in `Mathlib/Analysis/Calculus/Deriv/Add.lean`.
- `Real.exp` in `Mathlib/Analysis/SpecialFunctions/Exponential.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Air-water exchange: total inventory `ng + nw` is conserved to first
order, since `ng' = -J` and `nw' = J`. Here `J t = k * A * (H * p t - c t)`
with `p t = ng t * R * T / Vg` and `c t = nw t / Vw`. -/
theorem air_water_total_conserved (Vg Vw R T H k A : ℝ)
    (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    HasDerivAt (fun t => ng t + nw t) 0 t := by
  have h := hng.add hnw
  rw [neg_add_cancel] at h
  exact h

/-- The disequilibrium `d t = H * p t - c t` satisfies the linear decay
equation `d' t = -rate * d t` with
`rate = k * A * (H * R * T / Vg + 1 / Vw)`. -/
theorem air_water_difference_ode (Vg Vw R T H k A : ℝ)
    (hVg : 0 < Vg) (hVw : 0 < Vw)
    (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    HasDerivAt (fun t => H * (ng t * R * T / Vg) - nw t / Vw)
      (-(k * A * (H * R * T / Vg + 1 / Vw)) *
        (H * (ng t * R * T / Vg) - nw t / Vw)) t := by
  have _hVg_pos : 0 < Vg := hVg
  have _hVw_pos : 0 < Vw := hVw
  have h1 : HasDerivAt (fun t => ng t * R * T / Vg)
      (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) * R * T / Vg) t :=
    ((hng.mul_const R).mul_const T).div_const Vg
  have h2 : HasDerivAt (fun t => H * (ng t * R * T / Vg))
      (H * (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) * R * T / Vg)) t :=
    h1.const_mul H
  have h3 : HasDerivAt (fun t => nw t / Vw)
      ((k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) / Vw) t :=
    hnw.div_const Vw
  have h := h2.sub h3
  convert h using 1
  ring

/-- A function satisfying `d' t = -rate * d t` for all `t` decays
exponentially: `d t = d 0 * exp (-rate * t)`. -/
theorem exp_decay_of_linear_ode (d : ℝ → ℝ) (rate : ℝ)
    (hd : ∀ t, HasDerivAt d (-rate * d t) t) (t : ℝ) :
    d t = d 0 * Real.exp (-rate * t) := by
  have hlin : ∀ s, HasDerivAt (fun t => rate * t) rate s := fun s => by
    simpa using (hasDerivAt_id s).const_mul rate
  have hexp : ∀ s, HasDerivAt (fun t => Real.exp (rate * t))
      (Real.exp (rate * s) * rate) s := fun s => (hlin s).exp
  have he : ∀ s, HasDerivAt (fun t => d t * Real.exp (rate * t)) 0 s := fun s => by
    have h := (hd s).mul (hexp s)
    have hder : (-rate * d s) * Real.exp (rate * s)
        + d s * (Real.exp (rate * s) * rate) = 0 := by ring
    rw [hder] at h
    exact h
  have hdiff : Differentiable ℝ (fun t => d t * Real.exp (rate * t)) :=
    fun s => (he s).differentiableAt
  have hderiv : ∀ s, deriv (fun t => d t * Real.exp (rate * t)) s = 0 :=
    fun s => (he s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv t 0
  simp only [mul_zero, Real.exp_zero, mul_one] at hconst
  have h2 : Real.exp (rate * t) * Real.exp (-rate * t) = 1 := by
    have harg : rate * t + -rate * t = 0 := by ring
    calc Real.exp (rate * t) * Real.exp (-rate * t)
        = Real.exp (rate * t + -rate * t) := (Real.exp_add _ _).symm
      _ = 1 := by rw [harg, Real.exp_zero]
  calc d t = d t * 1 := (mul_one _).symm
    _ = d t * (Real.exp (rate * t) * Real.exp (-rate * t)) := by rw [h2]
    _ = (d t * Real.exp (rate * t)) * Real.exp (-rate * t) := by ring
    _ = d 0 * Real.exp (-rate * t) := by rw [hconst]

end EarthScience
