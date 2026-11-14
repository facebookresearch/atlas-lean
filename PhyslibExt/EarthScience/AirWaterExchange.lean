/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.ExponentialGrowth

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Air-water exchange with a conserved inventory

Closed isothermal two-compartment system: gas amount `ng` and dissolved
amount `nw` exchange through the flux `J = k * A * (H * p - c)` with
`p = ng * R * T / Vg` and `c = nw / Vw`, satisfying `ng' = -J` and
`nw' = J`. The flux is a transfer coefficient `k` times the interface area
`A` times the departure of the dissolved concentration `c` from its
Henry-law equilibrium value `H * p`, with `H` the solubility form of the
Henry constant (`c = H * p` at equilibrium) and `p` the ideal-gas partial
pressure. The total inventory `ng + nw` is conserved, and the
disequilibrium `d = H * p - c` satisfies the linear equation
`d' = -rate * d` with `rate = k * A * (H * R * T / Vg + 1 / Vw)`.

## i. Overview

Conservation is the cancellation of `+J` against `-J` in the derivative
of the total. The disequilibrium obeys a linear equation because
differentiating `H * p - c` pulls out one factor of the flux coefficient
from each compartment. Both identities hold for all real `k`, `A`, `H`,
`R`, `T` (the equation is stated for positive volumes), and a
disequilibrium satisfying the equation at every time is the signed
exponential `d(t) = d(0) * exp (-rate * t)`
(`MathlibExt.Analysis.ODE.ExponentialGrowth.eq_expGrowthPath_of_hasDerivAt`).
That exponential decays only when `rate > 0`; a negative rate would make
it grow. The rate is positive when the transfer coefficient `k`, the
interface area `A`, the Henry constant `H`, the gas constant `R`, the
absolute temperature `T` and both volumes are positive, and then the
disequilibrium tends to `0` in forward time. The model is a closed
isothermal ideal-gas/Henry system with constant geometry: no external
source or sink enters the budget.

## ii. Key results

- `EarthScience.air_water_total_hasDerivAt_zero`: total inventory derivative
  `0` at a time where the exchange equations hold.
- `EarthScience.air_water_total_conserved`: `ng t + nw t = ng 0 + nw 0` when
  the exchange equations hold at every time.
- `EarthScience.air_water_difference_ode`: the linear equation
  `d' = -rate * d`, for all real `k`, `A`, `H`, `R`, `T`.
- `EarthScience.air_water_difference_eq_expGrowthPath`: the signed
  exponential closed form `d(t) = d(0) * exp (-rate * t)`.
- `EarthScience.air_water_rate_pos`: `0 < rate` for positive physical
  parameters.
- `EarthScience.air_water_difference_tendsto_zero`: with positive physical
  parameters, the disequilibrium tends to `0` as `t → ∞`.

## iii. Table of contents

- A. Total inventory conservation
- B. Disequilibrium equation and closed form
- C. Physical decay

## iv. References

- P. S. Liss and P. G. Slater, *Flux of gases across the air-sea interface*,
  Nature 247 (1974), 181–184: the exchange flux as a transfer velocity times
  the departure of the dissolved concentration from its equilibrium value.
- R. Sander, *Compilation of Henry's law constants (version 4.0) for water as
  solvent*, Atmos. Chem. Phys. 15 (2015), 4399–4981: the solubility form
  `c = H * p` of the Henry constant.
- `expGrowthPath` and its uniqueness theorem in
  `MathlibExt/Analysis/ODE/ExponentialGrowth.lean`.
-/

@[expose] public section

namespace EarthScience

open MathlibExt.Analysis.ODE.ExponentialGrowth

/-! ## A. Total inventory conservation -/

/-- At a time `t` where `ng' = -J` and `nw' = J`, the total inventory
`ng + nw` has zero time derivative. Here `J t = k * A * (H * p t - c t)` with
`p t = ng t * R * T / Vg` and `c t = nw t / Vw`. -/
lemma air_water_total_hasDerivAt_zero (Vg Vw R T H k A : ℝ)
    (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    HasDerivAt (fun t => ng t + nw t) 0 t := by
  have h := hng.add hnw
  rw [neg_add_cancel] at h
  exact h

/-- Conservation of the total inventory: if the exchange equations hold at
every time, then `ng t + nw t = ng 0 + nw 0` for every `t`. -/
theorem air_water_total_conserved (Vg Vw R T H k A : ℝ) (ng nw : ℝ → ℝ)
    (hng : ∀ t, HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : ∀ t, HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t)
    (t : ℝ) :
    ng t + nw t = ng 0 + nw 0 := by
  have h := fun s =>
    air_water_total_hasDerivAt_zero Vg Vw R T H k A ng nw s (hng s) (hnw s)
  exact is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) t 0

/-! ## B. Disequilibrium equation and closed form -/

/-- The disequilibrium `d t = H * p t - c t` satisfies the linear equation
`d' t = -rate * d t` with `rate = k * A * (H * R * T / Vg + 1 / Vw)`.
The identity holds for all real `k`, `A`, `H`, `R`, `T`; it describes
relaxation toward equilibrium only when `rate > 0` (see
`air_water_rate_pos`). -/
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

/-- If the exchange equations hold at every time, the disequilibrium is the
signed exponential `d t = d 0 * exp (-rate * t)`, written as the exponential
path with rate `-rate`. No sign is imposed on `k`, `A`, `H`, `R`, `T`: for
`rate > 0` the path decays, for `rate < 0` it grows. -/
theorem air_water_difference_eq_expGrowthPath (Vg Vw R T H k A : ℝ)
    (hVg : 0 < Vg) (hVw : 0 < Vw) (ng nw : ℝ → ℝ)
    (hng : ∀ t, HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : ∀ t, HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t)
    (t : ℝ) :
    H * (ng t * R * T / Vg) - nw t / Vw =
      expGrowthPath (H * (ng 0 * R * T / Vg) - nw 0 / Vw)
        (-(k * A * (H * R * T / Vg + 1 / Vw))) t :=
  eq_expGrowthPath_of_hasDerivAt (x := fun t => H * (ng t * R * T / Vg) - nw t / Vw)
    (fun s => air_water_difference_ode Vg Vw R T H k A hVg hVw ng nw s (hng s) (hnw s)) t

/-! ## C. Physical decay -/

/-- With positive transfer coefficient `k`, interface area `A`, Henry
constant `H`, gas constant `R`, absolute temperature `T` and volumes `Vg`,
`Vw`, the relaxation rate `k * A * (H * R * T / Vg + 1 / Vw)` is positive. -/
lemma air_water_rate_pos (Vg Vw R T H k A : ℝ) (hVg : 0 < Vg) (hVw : 0 < Vw)
    (hR : 0 < R) (hT : 0 < T) (hH : 0 < H) (hk : 0 < k) (hA : 0 < A) :
    0 < k * A * (H * R * T / Vg + 1 / Vw) := by
  positivity

/-- Forward-time decay: with positive physical parameters and the exchange
equations holding at every time, the disequilibrium `H * p t - c t` tends
to `0` as `t → ∞`. -/
theorem air_water_difference_tendsto_zero (Vg Vw R T H k A : ℝ)
    (hVg : 0 < Vg) (hVw : 0 < Vw) (hR : 0 < R) (hT : 0 < T) (hH : 0 < H)
    (hk : 0 < k) (hA : 0 < A) (ng nw : ℝ → ℝ)
    (hng : ∀ t, HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : ∀ t, HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    Filter.Tendsto (fun t => H * (ng t * R * T / Vg) - nw t / Vw) Filter.atTop
      (nhds 0) := by
  have hrate := air_water_rate_pos Vg Vw R T H k A hVg hVw hR hT hH hk hA
  have hexp : Filter.Tendsto
      (fun t => Real.exp (-(k * A * (H * R * T / Vg + 1 / Vw)) * t)) Filter.atTop
      (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hrate))
  have hlim := hexp.const_mul (H * (ng 0 * R * T / Vg) - nw 0 / Vw)
  rw [mul_zero] at hlim
  refine hlim.congr fun t => ?_
  rw [air_water_difference_eq_expGrowthPath Vg Vw R T H k A hVg hVw ng nw hng hnw t,
    expGrowthPath]

end EarthScience
