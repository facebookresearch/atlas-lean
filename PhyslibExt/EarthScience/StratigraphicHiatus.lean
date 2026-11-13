/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stratigraphic hiatus: a jump in age, not a negative accumulation rate

Under constant accumulation speed `v`, with a hiatus at depth `h` that
removes `g` of time, the age at depth `d` is `d / v` above the hiatus and
`d / v + g` at and below it.

## i. Overview

A hiatus is missing time, not reversed deposition. The age function is
strictly increasing across every pair of depths, including pairs that
straddle the hiatus, so no accumulation rate is ever negative. The jump at
the hiatus itself is exactly `g`: the value at `h` exceeds the continuous
no-hiatus extension `h / v` by `g`, and the age difference across the
hiatus exceeds the constant-accumulation difference by `g`.

## ii. Key results

- `EarthScience.hiatusAge`: the age-depth model with a hiatus.
- `EarthScience.hiatus_age_below`, `EarthScience.hiatus_age_at_or_below`:
  the age on each side of the hiatus.
- `EarthScience.hiatus_age_strictMono`: age is strictly increasing in depth.
- `EarthScience.hiatus_age_jump`: the jump at the hiatus is exactly `g`.
- `EarthScience.hiatus_age_straddle`: across the hiatus the age difference
  is `(d₂ - d₁) / v + g`.

## iii. References

- `sub_div` for the age difference across the hiatus.
- `lt_add_of_pos_right` and `gcongr` for the strict monotonicity.
-/

@[expose] public section

namespace EarthScience

/-- Age at depth `d` under constant accumulation speed `v`, with a hiatus at
depth `h` that removes `g` of time: below the hiatus the age is `d / v`;
at and below (deeper than) the hiatus an extra `g` is added. -/
noncomputable def hiatusAge (v h g d : ℝ) : ℝ :=
  if d < h then d / v else d / v + g

/-- Below the hiatus the age is the ordinary constant-accumulation age. -/
theorem hiatus_age_below {v h g d : ℝ} (hd : d < h) :
    hiatusAge v h g d = d / v := by
  simp [hiatusAge, hd]

/-- At and below the hiatus the age is shifted up by the hiatus gap `g`. -/
theorem hiatus_age_at_or_below {v h g d : ℝ} (hd : h ≤ d) :
    hiatusAge v h g d = d / v + g := by
  simp [hiatusAge, not_lt.mpr hd]

/-- The hiatus is a jump, not a negative rate: age is strictly increasing
across every pair of depths, including pairs straddling the hiatus. -/
theorem hiatus_age_strictMono {v h g : ℝ} (hv : 0 < v) (hg : 0 < g) :
    StrictMono (hiatusAge v h g) := by
  intro a b hab
  unfold hiatusAge
  by_cases hb : b < h
  · have ha : a < h := lt_trans hab hb
    rw [ite_eq_left ha, ite_eq_left hb]
    gcongr
  · by_cases ha : a < h
    · rw [ite_eq_left ha, ite_eq_right hb]
      have hdiv : a / v < b / v := by gcongr
      have hadd : b / v < b / v + g := lt_add_of_pos_right _ hg
      linarith
    · rw [ite_eq_right ha, ite_eq_right hb]
      gcongr

/-- The jump at the hiatus is exactly `g`: the value at `h` exceeds the
continuous constant-accumulation extension `h / v` by `g`, so the age
function does not agree with the no-hiatus model at `h`. -/
theorem hiatus_age_jump {v h g : ℝ} :
    hiatusAge v h g h = h / v + g := by
  simp [hiatusAge]

set_option linter.unusedVariables false in
/-- No negative accumulation rate across the hiatus: for depths straddling
it, the age difference exceeds the constant-accumulation difference. -/
theorem hiatus_age_straddle {v h g d₁ d₂ : ℝ} (hv : 0 < v) (hg : 0 < g)
    (h1 : d₁ < h) (h2 : h ≤ d₂) :
    hiatusAge v h g d₂ - hiatusAge v h g d₁ = (d₂ - d₁) / v + g := by
  rw [hiatus_age_at_or_below h2, hiatus_age_below h1, sub_div]
  ring

end EarthScience
