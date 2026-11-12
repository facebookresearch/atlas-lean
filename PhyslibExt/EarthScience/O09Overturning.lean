/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Overturning and thermohaline box models

For a two-box exchange law `q = k * (alpha * DeltaT - beta * DeltaS)`,
upstream transport conserves total salt even when `q` changes sign:
box 1 loses `q * S1` if `q >= 0` (flow 1 to 2) and gains `-q * S2` if
`q < 0` (flow 2 to 1), and conversely for box 2. External forcing
`F1, F2` is kept separate, so the total salt `V1 * S1 + V2 * S2`
changes only through `F1 + F2`. At `q = 0` there is no advective
exchange. Equilibrium counts for the nonlinear model would need a
frozen forcing law / parameter region; no tipping claim is made here.

## i. Overview

Multiply each box balance by its volume, add, and cancel: in each sign
case the exchange terms are `q * S1` and `-q * S1` (or `q * S2` and
`-q * S2`).

## ii. Key results

- `EarthScience.stommel_exchange_sign`: sign of `q` follows `alpha * DeltaT - beta * DeltaS`.
- `EarthScience.overturning_total_salt_deriv`: total salt derivative is `F1 + F2`.
- `EarthScience.overturning_total_salt_deriv_zero_q`: flow-reversal boundary.

## iii. Table of contents

- A. Stommel exchange law and total-salt conservation

## iv. References

- `HasDerivAt.const_mul` / `HasDerivAt.add` in Mathlib.
- `mul_pos_iff_of_pos_left` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Stommel exchange law `q = k * (alpha * DeltaT - beta * DeltaS)`:
for `k > 0`, `q` has the sign of `alpha * DeltaT - beta * DeltaS`. -/
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

/-- Two-box overturning with signed exchange `q` and consistently defined
upstream transport: box 1 loses `q * S1` if `q >= 0` (flow 1 to 2) and
gains `-q * S2` if `q < 0` (flow 2 to 1), and conversely for box 2.
External forcing `F1, F2` is kept separate, so the total salt
`V1 * S1 + V2 * S2` changes only through `F1 + F2`, even when `q`
changes sign. -/
theorem overturning_total_salt_deriv {V1 V2 q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
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

/-- Flow-reversal boundary `q = 0`: there is no advective exchange, so
the total salt changes only through `F1 + F2`. -/
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
