/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Capped-triangular front speed bounds

## i. Overview

For the capped triangular flux
`q(k) = min (v * k) (min (w * (kj - k)) Qmax)` with `v, w, kj > 0`
and `Qmax ≥ 0`, every secant slope between distinct densities in
`[0, kj]` lies between `-w` and `v`. The rising branch has slope
`v`, the falling branch slope `-w`, and the capacity plateau
slope `0`; pointwise minima cannot produce a steeper secant,
including secants crossing a corner or the plateau.

## ii. Key results

- `capped_triangular_secant_bounds`: the two-sided secant bound.

## iii. Table of contents

- A. Secant bounds

## iv. References

- Standard traffic-flow theory (triangular fundamental diagram
  with capacity cap).
-/

@[expose] public section

/-! ## A. Secant bounds -/

namespace FluidDynamics.Traffic

/-- Capped-triangular front speed bounds. For the flux
`q(k) = min (v * k) (min (w * (kj - k)) Qmax)` with `v, w, kj > 0`
and `Qmax ≥ 0`, every secant slope between distinct densities in
`[0, kj]` lies between `-w` and `v`: the rising branch has slope
`v`, the falling branch slope `-w`, and the capacity plateau slope
`0`, and taking pointwise minima cannot produce a steeper secant,
including secants that cross a corner or the plateau. -/
theorem capped_triangular_secant_bounds {v w kj Qmax kL kR : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hkj : 0 < kj) (hQ : 0 ≤ Qmax)
    (hkL : kL ∈ Set.Icc 0 kj) (hkR : kR ∈ Set.Icc 0 kj)
    (hdist : kL ≠ kR) :
    -w ≤ (min (v * kR) (min (w * (kj - kR)) Qmax)
        - min (v * kL) (min (w * (kj - kL)) Qmax)) / (kR - kL)
      ∧ (min (v * kR) (min (w * (kj - kR)) Qmax)
        - min (v * kL) (min (w * (kj - kL)) Qmax)) / (kR - kL) ≤ v := by
  have hne : kR - kL ≠ 0 := sub_ne_zero.mpr (Ne.symm hdist)
  have _ : 0 < kj ∧ 0 ≤ Qmax ∧ kL ∈ Set.Icc 0 kj ∧ kR ∈ Set.Icc 0 kj :=
    ⟨hkj, hQ, hkL, hkR⟩
  have hR1 : min (v * kR) (min (w * (kj - kR)) Qmax) ≤ v * kR :=
    min_le_left _ _
  have hR2 : min (v * kR) (min (w * (kj - kR)) Qmax) ≤ w * (kj - kR) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hR3 : min (v * kR) (min (w * (kj - kR)) Qmax) ≤ Qmax :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hL1 : min (v * kL) (min (w * (kj - kL)) Qmax) ≤ v * kL :=
    min_le_left _ _
  have hL2 : min (v * kL) (min (w * (kj - kL)) Qmax) ≤ w * (kj - kL) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hL3 : min (v * kL) (min (w * (kj - kL)) Qmax) ≤ Qmax :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hwdiff : w * (kj - kR) - w * (kj - kL) = -(w * (kR - kL)) := by
    rw [mul_sub w kj kR, mul_sub w kj kL, mul_sub w kR kL,
      ← zero_sub (w * kR - w * kL), sub_eq_sub_iff_add_eq_add,
      sub_add_sub_cancel, zero_add]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- Case kR - kL < 0.
    have hle2n : v * (kR - kL) ≤ -(w * (kR - kL)) := by
      have h' : v * (kR - kL) + w * (kR - kL) ≤ 0 := by
        rw [← add_mul v w (kR - kL)]
        exact le_of_lt (mul_neg_of_pos_of_neg (add_pos hv hw) hneg)
      rw [← sub_neg_eq_add] at h'
      exact sub_nonpos.mp h'
    have hle2 : v * (kR - kL) ≤ -w * (kR - kL) := by
      rw [neg_mul w (kR - kL)]; exact hle2n
    have hnpv : v * (kR - kL) ≤ 0 :=
      le_of_lt (mul_neg_of_pos_of_neg hv hneg)
    have hnnw : (0:ℝ) ≤ -w * (kR - kL) := by
      rw [neg_mul w (kR - kL)]
      exact neg_nonneg_of_nonpos (le_of_lt (mul_neg_of_pos_of_neg hw hneg))
    constructor
    · rw [le_div_iff_of_neg hneg]
      rcases min_choice (v * kL) (min (w * (kj - kL)) Qmax) with hL | hL
      · rw [hL]
        exact le_trans (sub_le_sub_right hR1 _)
          (le_trans (le_of_eq (mul_sub v kR kL).symm) hle2)
      · rw [hL]
        rcases min_choice (w * (kj - kL)) Qmax with hL' | hL'
        · rw [hL']
          exact le_trans (sub_le_sub_right hR2 _)
            (le_trans (le_of_eq hwdiff) (le_of_eq (neg_mul w (kR - kL)).symm))
        · rw [hL']
          exact le_trans
            (le_trans (sub_le_sub_right hR3 _) (le_of_eq (sub_self Qmax))) hnnw
    · rw [div_le_iff_of_neg hneg]
      rcases min_choice (v * kR) (min (w * (kj - kR)) Qmax) with hR | hR
      · rw [hR]
        exact le_trans (le_of_eq (mul_sub v kR kL)) (sub_le_sub_left hL1 _)
      · rw [hR]
        rcases min_choice (w * (kj - kR)) Qmax with hR' | hR'
        · rw [hR']
          exact le_trans (le_trans hle2n (le_of_eq hwdiff.symm))
            (sub_le_sub_left hL2 _)
        · rw [hR']
          exact le_trans hnpv
            (le_trans (le_of_eq (sub_self Qmax).symm) (sub_le_sub_left hL3 _))
  · -- Case 0 < kR - kL.
    have hle1n : -(w * (kR - kL)) ≤ v * (kR - kL) := by
      rw [neg_le_iff_add_nonneg, ← add_mul v w (kR - kL)]
      exact mul_nonneg (le_of_lt (add_pos hv hw)) (le_of_lt hpos)
    have hle1 : -w * (kR - kL) ≤ v * (kR - kL) := by
      rw [neg_mul w (kR - kL)]; exact hle1n
    have hnnv : (0:ℝ) ≤ v * (kR - kL) :=
      mul_nonneg (le_of_lt hv) (le_of_lt hpos)
    have hnpw : -w * (kR - kL) ≤ 0 := by
      rw [neg_mul w (kR - kL)]
      exact neg_nonpos_of_nonneg (mul_nonneg (le_of_lt hw) (le_of_lt hpos))
    constructor
    · rw [le_div_iff₀ hpos]
      rcases min_choice (v * kR) (min (w * (kj - kR)) Qmax) with hR | hR
      · rw [hR]
        exact le_trans hle1
          (le_trans (le_of_eq (mul_sub v kR kL)) (sub_le_sub_left hL1 _))
      · rw [hR]
        rcases min_choice (w * (kj - kR)) Qmax with hR' | hR'
        · rw [hR']
          exact le_trans
            (le_trans (le_of_eq (neg_mul w (kR - kL))) (le_of_eq hwdiff.symm))
            (sub_le_sub_left hL2 _)
        · rw [hR']
          exact le_trans hnpw
            (le_trans (le_of_eq (sub_self Qmax).symm) (sub_le_sub_left hL3 _))
    · rw [div_le_iff₀ hpos]
      rcases min_choice (v * kL) (min (w * (kj - kL)) Qmax) with hL | hL
      · rw [hL]
        exact le_trans (sub_le_sub_right hR1 _)
          (le_of_eq (mul_sub v kR kL).symm)
      · rw [hL]
        rcases min_choice (w * (kj - kL)) Qmax with hL' | hL'
        · rw [hL']
          exact le_trans (sub_le_sub_right hR2 _)
            (le_trans (le_of_eq hwdiff) hle1n)
        · rw [hL']
          exact le_trans
            (le_trans (sub_le_sub_right hR3 _) (le_of_eq (sub_self Qmax))) hnnv

end FluidDynamics.Traffic
