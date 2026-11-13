/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Overturning and thermohaline box models

Two well-mixed boxes of fixed volumes `V1`, `V2` and salinities `S1`, `S2` exchange water
through an overturning circulation of transport `q`, after Stommel (1961). The exchange law
`q = k * (alpha * DeltaT - beta * DeltaS)` gives `q` the sign of
`alpha * DeltaT - beta * DeltaS`. In the closed loop, `q` carries the volume flux `|q|` from
one box to the other along one branch and back along the other, so each box receives `|q|`
of the other box's water and sends `|q|` of its own, whatever the sign of `q`. External salt
forcing `F1, F2` is kept separate, so the total salt `V1 * S1 + V2 * S2` changes only through
`F1 + F2`. A single directed upwind edge whose volume returns by a salt-free path conserves
total salt in the same way. At `q = 0` there is no advective exchange. Equilibrium counts for
the nonlinear model would need a frozen forcing law / parameter region; no tipping claim is
made here.

## i. Overview

Conventions: `DeltaT = T1 - T2` and `DeltaS = S1 - S2`. With a linear equation of state
`ρ = ρ₀ * (1 - alpha * T + beta * S)` (`alpha, beta > 0`),
`alpha * DeltaT - beta * DeltaS = (ρ2 - ρ1) / ρ₀`, so for `k > 0` the transport is positive
exactly when box 2 is denser, matching Stommel's flow law (transport proportional to the
density difference). `q > 0` is read as flow from box 1 to box 2 near the surface, returning
from box 2 to box 1 at depth; `q < 0` is the reverse.

Closed loop (`overturning_total_salt_deriv`): with upwind (donor-box) salinities, the balances
are `V1 * S1' = |q| * S2 - |q| * S1 + F1` and `V2 * S2' = |q| * S1 - |q| * S2 + F2`, the
exchange of Stommel's two-vessel model. For `q ≥ 0` the incoming flux `|q| * S2` of box 1 is
the deep return branch and its outgoing flux `|q| * S1` the surface branch; the roles swap for
`q < 0`. Multiply each balance by its volume and add: the exchange terms cancel.

One directed edge (`one_edge_upwind_total_salt_deriv`): generic upwind scalar transport along a
single edge, with box 1 losing `q * S1` to box 2 if `q ≥ 0` and gaining `-q * S2` from box 2
if `q < 0`. The volumes stay fixed only if the volume flux `|q|` carried by the edge returns by
another path; this identity assumes that path carries no salt (for example freshwater returned
through the atmosphere). It is not the closed overturning loop, whose return branch carries
salt.

## ii. Key results

- `EarthScience.stommel_exchange_sign`: sign of `q` follows `alpha * DeltaT - beta * DeltaS`.
- `EarthScience.overturning_total_salt_deriv`: closed overturning loop; total salt derivative
  is `F1 + F2`.
- `EarthScience.one_edge_upwind_total_salt_deriv`: one directed upwind edge with salt-free
  volume return; total salt derivative is `F1 + F2`.
- `EarthScience.overturning_total_salt_deriv_zero_q`: flow-reversal boundary.

## iii. Table of contents

- A. Stommel exchange law and total-salt conservation

## iv. References

- H. Stommel, *Thermohaline convection with two stable regimes of flow*, Tellus 13 (1961),
  224–230: two well-mixed vessels, flow proportional to their density difference, and an
  exchange of `|q|` between the vessels in each direction whatever the sign of the flow.
-/

@[expose] public section

namespace EarthScience


/-- Stommel exchange law `q = k * (alpha * DeltaT - beta * DeltaS)`:
for `k > 0`, `q` has the sign of `alpha * DeltaT - beta * DeltaS`, that is, of the density
difference `ρ2 - ρ1` (module conventions). -/
theorem stommel_exchange_sign {k alpha beta dT dS : ℝ} (hk : 0 < k) :
    (0 < k * (alpha * dT - beta * dS) ↔ 0 < alpha * dT - beta * dS) ∧
      (k * (alpha * dT - beta * dS) = 0 ↔ alpha * dT - beta * dS = 0) ∧
        (k * (alpha * dT - beta * dS) < 0 ↔ alpha * dT - beta * dS < 0) := by
  refine ⟨mul_pos_iff_of_pos_left hk, ?_, ?_⟩
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with hk0 | hx0
      · exact absurd hk0 (ne_of_gt hk)
      · exact hx0
    · intro h
      rw [h, mul_zero]
  · constructor
    · intro h
      by_contra hcon
      have hle : 0 ≤ alpha * dT - beta * dS := not_lt.mp hcon
      have hnn : 0 ≤ k * (alpha * dT - beta * dS) := mul_nonneg hk.le hle
      exact absurd h (not_lt_of_ge hnn)
    · exact fun h => mul_neg_of_pos_of_neg hk h

/-- **Closed two-box overturning loop** (Stommel 1961). The transport `q` carries the volume
flux `|q|` from one box to the other along one branch and back along the other, so with
upwind (donor-box) salinities each box receives `|q|` times the other box's salinity and loses
`|q|` times its own, whatever the sign of `q`:
`V1 * S1' = |q| * S2 - |q| * S1 + F1` and `V2 * S2' = |q| * S1 - |q| * S2 + F2`. The volumes
stay fixed, and the total salt `V1 * S1 + V2 * S2` changes only through the external forcing
`F1 + F2`. -/
theorem overturning_total_salt_deriv {V1 V2 q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((|q| * S2 t - |q| * S1 t) / V1 + F1 / V1) t)
    (h2 : HasDerivAt S2 ((|q| * S1 t - |q| * S2 t) / V2 + F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t := by
  have hV1' : V1 ≠ 0 := ne_of_gt hV1
  have hV2' : V2 ≠ 0 := ne_of_gt hV2
  have h := (h1.const_mul V1).add (h2.const_mul V2)
  have heq : V1 * ((|q| * S2 t - |q| * S1 t) / V1 + F1 / V1) +
      V2 * ((|q| * S1 t - |q| * S2 t) / V2 + F2 / V2) = F1 + F2 := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- One directed upwind edge between the boxes (generic scalar transport, not the closed
overturning loop): box 1 loses `q * S1` if `q >= 0` (flow 1 to 2) and gains `-q * S2` if
`q < 0` (flow 2 to 1), and conversely for box 2. The volume flux `|q|` carried by the edge is
assumed to return by a salt-free path, so the volumes stay fixed and only this salt flux
crosses between the boxes; in the closed loop `overturning_total_salt_deriv` the return branch
carries salt too. External forcing `F1, F2` is kept separate, so the total salt
`V1 * S1 + V2 * S2` changes only through `F1 + F2`, even when `q` changes sign. -/
theorem one_edge_upwind_total_salt_deriv {V1 V2 q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((if 0 ≤ q then -q * S1 t else -q * S2 t) / V1 + F1 / V1) t)
    (h2 : HasDerivAt S2 ((if 0 ≤ q then q * S1 t else q * S2 t) / V2 + F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t := by
  have hV1' : V1 ≠ 0 := ne_of_gt hV1
  have hV2' : V2 ≠ 0 := ne_of_gt hV2
  have h := (h1.const_mul V1).add (h2.const_mul V2)
  have heq : V1 * ((if 0 ≤ q then -q * S1 t else -q * S2 t) / V1 + F1 / V1) +
      V2 * ((if 0 ≤ q then q * S1 t else q * S2 t) / V2 + F2 / V2) = F1 + F2 := by
    by_cases hq : 0 ≤ q <;> simp [hq] <;> field_simp <;> ring
  rw [heq] at h
  exact h

/-- Flow-reversal boundary `q = 0`: there is no advective exchange (in the closed loop and on
a single edge alike), so the total salt changes only through `F1 + F2`. -/
theorem overturning_total_salt_deriv_zero_q {V1 V2 F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 (F1 / V1) t)
    (h2 : HasDerivAt S2 (F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t := by
  have hV1' : V1 ≠ 0 := ne_of_gt hV1
  have hV2' : V2 ≠ 0 := ne_of_gt hV2
  have h := (h1.const_mul V1).add (h2.const_mul V2)
  have heq : V1 * (F1 / V1) + V2 * (F2 / V2) = F1 + F2 := by
    field_simp
  rw [heq] at h
  exact h

end EarthScience
