/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exposure ages: monotone inventory and its admissible age inverse

With constant production `P` and decay constant `lam`, the nuclide
inventory
`N(t) = N0 * exp (-lam * t) + (P / lam) * (1 - exp (-lam * t))`
rises toward the saturation value `P / lam` when it starts below it, and
the exposure age inverts it at `N0 = 0`.

## i. Overview

Rewriting the inventory as `P / lam + (N0 - P / lam) * exp (-lam * t)`
makes the behaviour visible: the exponential decays, so when
`N0 ≤ P / lam` the inventory is monotone on nonnegative time, and when
`N0 < P / lam` it is strictly increasing, always staying at or below
saturation. For `N0 = 0` and admissible inventories `0 ≤ N < P / lam`,
the age `-log (1 - lam * N / P) / lam` inverts the inventory in both
directions: evaluating the inventory at the age of `N` returns `N`, and
taking the age of the inventory at time `t` returns `t`.

## ii. Key results

- `EarthScience.exposureInventory`, `EarthScience.exposureAge`: the
  inventory and its age inverse.
- `EarthScience.exposure_inventory_monotoneOn`,
  `EarthScience.exposure_inventory_strictMonoOn`: monotonicity below
  saturation.
- `EarthScience.exposure_inventory_le_saturation`: the saturation bound.
- `EarthScience.exposure_age_inventory`,
  `EarthScience.exposure_inventory_age`: the two directions of the inverse.

## iii. References

- `Real.exp_le_exp_of_le`, `Real.exp_lt_exp` for monotonicity of the
  exponential.
- `Real.exp_log`, `Real.log_exp` for the logarithmic inverse.
- `div_lt_one`, `lt_div_iff₀` for the admissibility bounds.
-/

@[expose] public section

namespace EarthScience

/-- Exposure inventory with constant production `P`, decay `lam`,
inherited inventory `N0`: `N0 * exp (-lam * t) + (P / lam) * (1 - exp (-lam * t))`. -/
noncomputable def exposureInventory (P lam N0 t : ℝ) : ℝ :=
  N0 * Real.exp (-lam * t) + (P / lam) * (1 - Real.exp (-lam * t))

/-- Exposure age inverting the inventory at `N0 = 0`:
`-log (1 - lam * N / P) / lam`. Admissible for `0 ≤ N < P / lam`. -/
noncomputable def exposureAge (P lam N : ℝ) : ℝ :=
  -Real.log (1 - lam * N / P) / lam

/-- The inventory in saturation form:
`P / lam + (N0 - P / lam) * exp (-lam * t)`. -/
private theorem exposureInventory_eq (P lam N0 t : ℝ) :
    exposureInventory P lam N0 t = P / lam + (N0 - P / lam) * Real.exp (-lam * t) := by
  unfold exposureInventory
  ring

/-- Below saturation the inventory is monotone on nonnegative time:
it never decreases toward saturation from below. -/
theorem exposure_inventory_monotoneOn {P lam N0 : ℝ} (_hP : 0 < P)
    (hlam : 0 < lam) (hN0 : N0 ≤ P / lam) :
    MonotoneOn (exposureInventory P lam N0) (Set.Ici 0) := by
  intro a _ha b _hb hab
  have h1 : lam * a ≤ lam * b := by
    apply mul_le_mul_of_nonneg_left hab (le_of_lt hlam)
  have h2 : -lam * b ≤ -lam * a := by linarith
  have hE : Real.exp (-lam * b) ≤ Real.exp (-lam * a) :=
    Real.exp_le_exp_of_le h2
  have hC : (0 : ℝ) ≤ P / lam - N0 := by linarith
  have hmul : (P / lam - N0) * Real.exp (-lam * b) ≤ (P / lam - N0) * Real.exp (-lam * a) :=
    mul_le_mul_of_nonneg_left hE hC
  have e1 := exposureInventory_eq P lam N0 a
  have e2 := exposureInventory_eq P lam N0 b
  nlinarith [hmul, e1, e2]

/-- Strictly below saturation the inventory is strictly increasing. -/
theorem exposure_inventory_strictMonoOn {P lam N0 : ℝ} (_hP : 0 < P)
    (hlam : 0 < lam) (hN0 : N0 < P / lam) :
    StrictMonoOn (exposureInventory P lam N0) (Set.Ici 0) := by
  intro a _ha b _hb hab
  have h1 : lam * a < lam * b := mul_lt_mul_of_pos_left hab hlam
  have h2 : -lam * b < -lam * a := by linarith
  have hE : Real.exp (-lam * b) < Real.exp (-lam * a) :=
    Real.exp_lt_exp.mpr h2
  have hC : (0 : ℝ) < P / lam - N0 := by linarith
  have hmul : (P / lam - N0) * Real.exp (-lam * b) < (P / lam - N0) * Real.exp (-lam * a) :=
    mul_lt_mul_of_pos_left hE hC
  have e1 := exposureInventory_eq P lam N0 a
  have e2 := exposureInventory_eq P lam N0 b
  nlinarith [hmul, e1, e2]

/-- The inventory is bounded above by the saturation value `P / lam`. -/
theorem exposure_inventory_le_saturation {P lam N0 : ℝ} (_hP : 0 < P)
    (_hlam : 0 < lam) (_hN0 : 0 ≤ N0) (hN0' : N0 ≤ P / lam) (t : ℝ) (_ht : 0 ≤ t) :
    exposureInventory P lam N0 t ≤ P / lam := by
  have hE : (0 : ℝ) ≤ Real.exp (-lam * t) := le_of_lt (Real.exp_pos _)
  have hC : (N0 - P / lam) ≤ (0 : ℝ) := by linarith
  have hmul : (N0 - P / lam) * Real.exp (-lam * t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hC hE
  have e := exposureInventory_eq P lam N0 t
  nlinarith [hmul, e]

/-- The age inverse recovers the inventory: at `N0 = 0`, evaluating the
inventory at the exposure age of an admissible `N` returns `N`. -/
theorem exposure_age_inventory {P lam N : ℝ} (hP : 0 < P) (hlam : 0 < lam)
    (_hN : 0 ≤ N) (hN' : N < P / lam) :
    exposureInventory P lam 0 (exposureAge P lam N) = N := by
  have hP_ne : P ≠ 0 := ne_of_gt hP
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hNlam : N * lam < P := (lt_div_iff₀ hlam).mp hN'
  have hlamN : lam * N < P := by linarith
  have hdiv : lam * N / P < 1 := (div_lt_one hP).mpr hlamN
  have harg : (0 : ℝ) < 1 - lam * N / P := by linarith
  have hlog : -lam * exposureAge P lam N = Real.log (1 - lam * N / P) := by
    unfold exposureAge
    field_simp
  have hexp : Real.exp (-lam * exposureAge P lam N) = 1 - lam * N / P := by
    rw [hlog]
    exact Real.exp_log harg
  unfold exposureInventory
  rw [hexp]
  field_simp
  ring

/-- The inventory followed by the age inverse recovers the time. -/
theorem exposure_inventory_age {P lam t : ℝ} (hP : 0 < P) (hlam : 0 < lam)
    (_ht : 0 ≤ t) :
    exposureAge P lam (exposureInventory P lam 0 t) = t := by
  have hP_ne : P ≠ 0 := ne_of_gt hP
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have harg_eq : 1 - lam * exposureInventory P lam 0 t / P = Real.exp (-lam * t) := by
    unfold exposureInventory
    field_simp
    ring
  have hlog : Real.log (1 - lam * exposureInventory P lam 0 t / P) = -lam * t := by
    rw [harg_eq]
    exact Real.log_exp _
  unfold exposureAge
  rw [hlog]
  field_simp

end EarthScience
