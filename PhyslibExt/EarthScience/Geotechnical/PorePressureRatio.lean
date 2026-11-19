/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Excess pore-pressure ratio

## i. Overview

At a fixed compression-positive total stress `σc`, the vertical
effective stress at time `t` is the `(k, k)` entry of
`effectiveStressCompressionPositive σc (u t)`, where `u` is the
pore-pressure series in the same stress unit and `k` indexes the
vertical axis. The excess pore-pressure ratio is the
Seed–Idriss observation coordinate
`r_u(t) = (u t - u 0) / σ'_v(0)`, with reference pressure `u 0`
at the time origin. It is not the Bishop–Morgenstern slope
coefficient `u / (γ h)`. The physical validity domain of
the ratio is positive initial effective stress
`σ'_v(0) > 0`; the definition itself uses totalized real
division, so at `σ'_v(0) = 0` it returns `0` by
totalization and carries no physical reading there. On the
validity domain, the identities
`σ'_v(t) = σ'_v(0) (1 - r_u(t))` and `r_u(t) = 1 ↔ σ'_v(t) = 0`
hold (their positivity hypotheses are exactly this validity
condition); they are observation-coordinate identities
only: no liquefaction or failure criterion is claimed.

## ii. Key results

- `EarthScience.verticalEffectiveStress` and
  `excessPorePressureRatio`: the vertical effective stress and
  ratio.
- `EarthScience.verticalEffectiveStress_eq_mul_one_sub_ratio`:
  the ratio parametrization of vertical effective stress.
- `EarthScience.excessPorePressureRatio_eq_one_iff`: unit ratio
  exactly at zero vertical effective stress.

## iii. Table of contents

- A. Vertical effective stress and ratio

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.EffectiveStress` for
  the compression-positive effective stress at Biot coefficient
  one.
- H. B. Seed and I. M. Idriss, *Simplified Procedure for
  Evaluating Soil Liquefaction Potential*, Journal of the Soil
  Mechanics and Foundations Division, ASCE 97(9), 1971: the
  excess pore-pressure ratio `Δu / σ'_v0`.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Vertical effective stress and ratio -/

/-- Vertical effective stress at time `t`: the `(k, k)` entry of
the compression-positive effective stress of the fixed total
stress `σc` at pore pressure `u t`. -/
def verticalEffectiveStress {n : ℕ} (σc : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  effectiveStressCompressionPositive σc (u t) k k

/-- Excess pore-pressure ratio `r_u(t) = (u t - u 0) / σ'_v(0)`
(totalized real division; the physical validity domain is
`σ'_v(0) > 0`, outside which the value is totalization
junk). -/
noncomputable def excessPorePressureRatio {n : ℕ}
    (σc : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (u t - u 0) / verticalEffectiveStress σc k u 0

/-- Bridge: the vertical effective stress is `σc k k - u t`. -/
lemma verticalEffectiveStress_eq {n : ℕ} (σc : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) (u : ℝ → ℝ) (t : ℝ) :
    verticalEffectiveStress σc k u t = σc k k - u t := by
  simp [verticalEffectiveStress, effectiveStressCompressionPositive]

/-- `σ'_v(t) = σ'_v(0) * (1 - r_u(t))`. -/
theorem verticalEffectiveStress_eq_mul_one_sub_ratio {n : ℕ}
    {σc : Matrix (Fin n) (Fin n) ℝ} {k : Fin n} {u : ℝ → ℝ}
    (h0 : 0 < verticalEffectiveStress σc k u 0) (t : ℝ) :
    verticalEffectiveStress σc k u t
      = verticalEffectiveStress σc k u 0
        * (1 - excessPorePressureRatio σc k u t) := by
  have hσ : ∀ s : ℝ, verticalEffectiveStress σc k u s = σc k k - u s :=
    fun s => verticalEffectiveStress_eq σc k u s
  rw [hσ t, hσ 0]
  unfold excessPorePressureRatio
  rw [hσ 0]
  have hne : σc k k - u 0 ≠ 0 := by
    rw [← hσ 0]
    exact ne_of_gt h0
  field_simp
  ring

/-- `r_u(t) = 1 ↔ σ'_v(t) = 0`. -/
theorem excessPorePressureRatio_eq_one_iff {n : ℕ}
    {σc : Matrix (Fin n) (Fin n) ℝ} {k : Fin n} {u : ℝ → ℝ}
    (h0 : 0 < verticalEffectiveStress σc k u 0) (t : ℝ) :
    excessPorePressureRatio σc k u t = 1
      ↔ verticalEffectiveStress σc k u t = 0 := by
  have hσ : ∀ s : ℝ, verticalEffectiveStress σc k u s = σc k k - u s :=
    fun s => verticalEffectiveStress_eq σc k u s
  have hne : σc k k - u 0 ≠ 0 := by
    rw [← hσ 0]
    exact ne_of_gt h0
  unfold excessPorePressureRatio
  rw [hσ 0, hσ t]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

end EarthScience
