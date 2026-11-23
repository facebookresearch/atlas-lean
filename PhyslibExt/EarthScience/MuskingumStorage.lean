/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Muskingum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Muskingum storage balance

## i. Overview

With Muskingum storage `S = K * (X * I + (1 - X) * O)` and the
routing coefficients of `PhyslibExt.EarthScience.Muskingum`, the
one-step recurrence for the current outflow is, under a nonzero
denominator, equivalent to the trapezoidal storage balance
`S1 - S0 = dt * ((I1 + I0) - (O1 + O0)) / 2`. Under the
nonnegative-coefficient admissibility window the routed outflow
is a convex combination of its three inputs, so an interval
containing the two inflows and the previous outflow also
contains the routed outflow.

## ii. Key results

- `EarthScience.muskingum_storage_balance_iff`: recurrence
  versus trapezoidal storage balance.
- `EarthScience.muskingum_outflow_mem_Icc`: interval invariance
  of the routed outflow.

## iii. Table of contents

- A. Storage and one-step balance

## iv. References

- V. T. Chow, D. R. Maidment and L. W. Mays, *Applied
  Hydrology*, McGraw-Hill, 1988 (Muskingum routing).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Storage and one-step balance -/

/-- Muskingum storage `S = K * (X * I + (1 - X) * O)` for inflow
`I` and outflow `O`. -/
noncomputable def muskingumStorage (K X I O : ℝ) : ℝ :=
  K * (X * I + (1 - X) * O)

/-- One-step storage-balance correspondence: with a nonzero
Muskingum denominator, the routing recurrence for the current
outflow is equivalent to the trapezoidal storage balance over
one step. -/
theorem muskingum_storage_balance_iff {K X dt I0 I1 O0 O1 : ℝ}
    (hden : muskingumDenominator K X dt ≠ 0) :
    (O1 = muskingumC0 K X dt * I1 + muskingumC1 K X dt * I0
        + muskingumC2 K X dt * O0)
      ↔ muskingumStorage K X I1 O1 - muskingumStorage K X I0 O0
        = dt * ((I1 + I0) - (O1 + O0)) / 2 := by
  have hden' : 2 * K * (1 - X) + dt ≠ 0 := hden
  have key : muskingumDenominator K X dt
        * (O1 - (muskingumC0 K X dt * I1 + muskingumC1 K X dt * I0
          + muskingumC2 K X dt * O0))
      = 2 * ((muskingumStorage K X I1 O1 - muskingumStorage K X I0 O0)
        - dt * ((I1 + I0) - (O1 + O0)) / 2) := by
    simp only [muskingumDenominator, muskingumC0, muskingumC1, muskingumC2,
      muskingumStorage]
    field_simp
    ring
  have key0 : (O1 - (muskingumC0 K X dt * I1 + muskingumC1 K X dt * I0
        + muskingumC2 K X dt * O0) = 0)
      ↔ ((muskingumStorage K X I1 O1 - muskingumStorage K X I0 O0)
        - dt * ((I1 + I0) - (O1 + O0)) / 2 = 0) := by
    constructor
    · intro h0
      have h2 : (2 : ℝ) * ((muskingumStorage K X I1 O1
          - muskingumStorage K X I0 O0)
          - dt * ((I1 + I0) - (O1 + O0)) / 2) = 0 := by
        rw [← key, h0, mul_zero]
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    · intro h0
      have hD : muskingumDenominator K X dt * (O1
          - (muskingumC0 K X dt * I1 + muskingumC1 K X dt * I0
            + muskingumC2 K X dt * O0)) = 0 := by
        rw [key, h0, mul_zero]
      exact (mul_eq_zero.mp hD).resolve_left hden
  simp only [sub_eq_zero] at key0
  exact key0

/-- Bounded-outflow invariance: for `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0`
in the nonnegative-coefficient admission range
`2 * K * X ≤ dt ≤ 2 * K * (1 - X)`, if the two inflows and previous
outflow lie in `[a, b]`, so does the routed outflow (a convex
combination). -/
theorem muskingum_outflow_mem_Icc {K X dt I0 I1 O0 a b : ℝ}
    (hK : 0 < K) (hX0 : 0 ≤ X) (hX : X ≤ 1 / 2) (hdt : 0 < dt)
    (hadm : 2 * K * X ≤ dt ∧ dt ≤ 2 * K * (1 - X))
    (hI1 : I1 ∈ Set.Icc a b) (hI0 : I0 ∈ Set.Icc a b)
    (hO0 : O0 ∈ Set.Icc a b) :
    muskingumC0 K X dt * I1 + muskingumC1 K X dt * I0
        + muskingumC2 K X dt * O0 ∈ Set.Icc a b := by
  obtain ⟨h0, h1, h2⟩ := (muskingum_nonneg_iff hK hX0 hX hdt).mpr hadm
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hden_pos : 0 < muskingumDenominator K X dt := by
    simp only [muskingumDenominator]
    have hKX : (0 : ℝ) < 2 * K * (1 - X) := by positivity
    linarith
  have hsum : muskingumC0 K X dt + muskingumC1 K X dt
      + muskingumC2 K X dt = 1 :=
    muskingum_coefficients_sum (ne_of_gt hden_pos)
  obtain ⟨ha1, h1b⟩ := Set.mem_Icc.mp hI1
  obtain ⟨ha0, h0b⟩ := Set.mem_Icc.mp hI0
  obtain ⟨haO, hOb⟩ := Set.mem_Icc.mp hO0
  have e : ∀ t : ℝ, muskingumC0 K X dt * t + muskingumC1 K X dt * t
      + muskingumC2 K X dt * t = t := by
    intro t
    have hsuma : (muskingumC0 K X dt + muskingumC1 K X dt
        + muskingumC2 K X dt) * t = t := by
      rw [hsum, one_mul]
    simp only [add_mul] at hsuma
    exact hsuma
  rw [Set.mem_Icc]
  constructor
  · rw [← e a]
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left ha1 h0)
        (mul_le_mul_of_nonneg_left ha0 h1))
      (mul_le_mul_of_nonneg_left haO h2)
  · rw [← e b]
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left h1b h0)
        (mul_le_mul_of_nonneg_left h0b h1))
      (mul_le_mul_of_nonneg_left hOb h2)

end EarthScience
