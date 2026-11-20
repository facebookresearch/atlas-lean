/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Elasticity.ColumnBuckling
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Column buckling checks

Concrete consumers of `PhyslibExt.Elasticity.ColumnBuckling`: the
unit-shape clamped-clamped mode at `L = 2`, its equation at a point, the
pinned sine that fails the clamped slope condition, and pinned-pinned
energy-threshold checks for a polynomial deflection and the sine mode.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Clamped-clamped mode at `L = 2`
- B. A pinned sine is not clamped
- C. Pinned-pinned energy threshold

## iv. References

- `PhyslibExt.Elasticity.ColumnBuckling`
-/

/-- Midspan value at `L = 2`: the mode value at `x = 1` is `2`. -/
example : Elasticity.clampedClampedMode 2 1 = 2 := by
  have h := Elasticity.clampedClampedMode_midspan (L := 2) (by norm_num)
  norm_num at h
  exact h

/-- The column equation at the midspan point for `EI = 3`, `L = 2`. -/
example :
    3 * iteratedDeriv 4 (Elasticity.clampedClampedMode 2) 1 +
        (4 * Real.pi ^ 2 * 3 / 2 ^ 2) *
          iteratedDeriv 2 (Elasticity.clampedClampedMode 2) 1 = 0 :=
  (Elasticity.clampedClamped_eigenpair (EI := 3) (L := 2) (by norm_num) (by norm_num)).1 1

/-- Boundary failure: the pinned-pinned sine `sin (πx / 2)` on `L = 2`
has slope `π / 2 ≠ 0` at `x = 0`, so it does not meet the clamped slope
condition. -/
example : deriv (fun x : ℝ => Real.sin (Real.pi * x / 2)) 0 ≠ 0 := by
  have h1 : HasDerivAt (fun x : ℝ => Real.pi * x / 2) (Real.pi / 2) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (Real.pi / 2)
    rw [mul_one] at h
    have heq : (fun x : ℝ => Real.pi * x / 2)
        = fun x : ℝ => (Real.pi / 2) * x := by
      funext y
      ring
    rwa [heq]
  have hd := h1.sin.deriv
  have hval : Real.cos (Real.pi * (0 : ℝ) / 2) * (Real.pi / 2)
      = Real.pi / 2 := by simp
  rw [hd, hval]
  exact div_ne_zero (ne_of_gt Real.pi_pos) two_ne_zero

/-- Tip value at `L = 2`: the clamped-free mode value at the free end
is `1`. -/
example : Elasticity.clampedFreeMode 2 2 = 1 :=
  Elasticity.clampedFreeMode_tip (by norm_num)

/-- The clamped-free column equation at a point for `EI = 3`, `L = 2`,
and its free-end shear-moment trace `EI * w'''(L) + P * w'(L) = 0`
with nonzero tip slope `w'(L) = π / 4`. -/
example :
    (3 * iteratedDeriv 4 (Elasticity.clampedFreeMode 2) 1 +
        (Real.pi ^ 2 * 3 / (4 * 2 ^ 2)) *
          iteratedDeriv 2 (Elasticity.clampedFreeMode 2) 1 = 0) ∧
      (3 * iteratedDeriv 3 (Elasticity.clampedFreeMode 2) 2 +
          (Real.pi ^ 2 * 3 / (4 * 2 ^ 2)) *
            deriv (Elasticity.clampedFreeMode 2) 2 = 0) ∧
        deriv (Elasticity.clampedFreeMode 2) 2 = Real.pi / 4 := by
  have h := Elasticity.clampedFree_eigenpair (EI := 3) (L := 2)
    (by norm_num) (by norm_num)
  refine ⟨h.1 1, h.2.2.2.2, ?_⟩
  rw [Elasticity.deriv_clampedFreeMode (L := 2) (by norm_num)]
  show Real.pi / (2 * 2) * Real.sin (Real.pi * 2 / (2 * 2)) = Real.pi / 4
  have hph : Real.pi * (2 : ℝ) / (2 * 2) = Real.pi / 2 := by ring
  rw [hph, Real.sin_pi_div_two]
  ring


/-- Integration by parts and subcritical positivity for the polynomial
deflection `w(x) = x * (1 - x)` on `[0, 1]`, with `w' = 1 - 2x` and
`w'' = -2`. The second component is at `EI = 1` and zero axial load. -/
example : (∫ x in (0 : ℝ)..1, (1 - 2 * x) ^ 2) =
      -∫ x in (0 : ℝ)..1, (x * (1 - x)) * (-2) ∧
    0 < (1 : ℝ) * (∫ x in (0 : ℝ)..1, (-2 : ℝ) ^ 2) -
      0 * ∫ x in (0 : ℝ)..1, (1 - 2 * x) ^ 2 := by
  have hw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
    intro x _
    have h : HasDerivAt (fun x : ℝ => x * (1 - x))
        (1 * (1 - x) + x * (0 - 1)) x := by
      apply HasDerivAt.mul
      · exact hasDerivAt_id x
      · exact (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hv : (1 : ℝ) * (1 - x) + x * (0 - 1) = 1 - 2 * x := by ring
    rwa [hv] at h
  have hw' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) x := by
    intro x _
    have h : HasDerivAt (fun x : ℝ => 1 - 2 * x) (0 - 2 * 1) x := by
      apply HasDerivAt.sub
      · exact hasDerivAt_const x (1 : ℝ)
      · exact (hasDerivAt_id x).const_mul (2 : ℝ)
    have hv : (0 : ℝ) - 2 * 1 = -2 := by ring
    rwa [hv] at h
  have hw'' : ContinuousOn (fun _ : ℝ => (-2 : ℝ)) (Set.Icc 0 1) :=
    continuousOn_const
  refine ⟨Elasticity.integral_deriv_sq_eq_neg one_pos hw hw' hw''
    (by norm_num) (by norm_num), ?_⟩
  exact Elasticity.quadratic_energy_pos_of_lt one_pos one_pos
    (by
      have hπ : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
      simpa using hπ)
    hw hw' hw'' (by norm_num) (by norm_num)
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- At `EI = L = 1`, the pinned sine mode has zero quadratic energy at
the critical load. -/
example : (1 : ℝ) * (∫ x in (0 : ℝ)..1,
      (iteratedDeriv 2 (Elasticity.pinnedMode 1) x) ^ 2) -
      (Real.pi ^ 2 * 1 / 1 ^ 2) * (∫ x in (0 : ℝ)..1,
        (deriv (Elasticity.pinnedMode 1) x) ^ 2) = 0 :=
  Elasticity.pinnedMode_energy_eq_zero one_pos one_pos

/-- At `EI = L = 1` and load `π^2 + 1`, the pinned sine mode has
strictly negative quadratic energy. -/
example : (1 : ℝ) * (∫ x in (0 : ℝ)..1,
      (iteratedDeriv 2 (Elasticity.pinnedMode 1) x) ^ 2) -
      (Real.pi ^ 2 + 1) * (∫ x in (0 : ℝ)..1,
        (deriv (Elasticity.pinnedMode 1) x) ^ 2) < 0 :=
  Elasticity.pinnedMode_energy_neg one_pos one_pos (by
    have hπ : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
    simp only [mul_one, one_pow, div_one]
    linarith)
