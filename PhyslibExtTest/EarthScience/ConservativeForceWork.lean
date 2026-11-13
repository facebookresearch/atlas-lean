/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ConservativeForceWork
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory intervalIntegral

/-!
# Conservative-force work checks

Concrete consumers of `PhyslibExt.EarthScience.ConservativeForceWork`:
a linear potential `U x = 3 * x` on `ℝ` with constant force `F = -3`
along the path `γ t = 2 * t` from `t = 0` to `t = 1`, and the
degenerate-interval boundary case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. In the
concrete case the work integral is `∫₀¹ (-3) * 2 = -6` and the
potential decrease is `-(U 2 - U 0) = -6`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear potential, constant force
- B. Degenerate interval

## iv. References

- `PhyslibExt.EarthScience.ConservativeForceWork`
-/

/-- Public shape of the conservative-force work theorem. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {U : E → ℝ} {g F : E → E} {γ γ' : ℝ → E}
    (hF : ∀ x, F x = -g x)
    (hgrad : ∀ x, HasFDerivAt U (InnerProductSpace.toDual ℝ E (g x)) x)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hInt : IntervalIntegrable (fun t => inner ℝ (F (γ t)) (γ' t)) volume a b) :
    ∫ t in a..b, inner ℝ (F (γ t)) (γ' t) = -(U (γ b) - U (γ a)) :=
  EarthScience.conservative_force_work_eq_potential_decrease hF hgrad hγ hInt

set_option linter.unusedVariables false in
/-- Linear potential `U x = 3 * x`, constant force `-3`, path `γ t = 2 * t`:
the work integral is `-6`, the potential decrease is `-6`. -/
example : ∫ t in (0 : ℝ)..1, inner ℝ ((-3 : ℝ)) (2 : ℝ) = -6 := by
  have hF : ∀ x : ℝ, (fun _ : ℝ => (-3 : ℝ)) x = -(fun _ : ℝ => (3 : ℝ)) x := fun _ => rfl
  have hgrad : ∀ x : ℝ, HasFDerivAt (fun x : ℝ => 3 * x)
      (InnerProductSpace.toDual ℝ ℝ ((fun _ : ℝ => (3 : ℝ)) x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 3 * x) 3 x := by
      simpa using (hasDerivAt_id x).const_mul (3 : ℝ)
    have h2 := h1.hasFDerivAt
    convert h2 using 1
    apply ContinuousLinearMap.ext
    intro y
    simp [InnerProductSpace.toDual_apply_apply]
  have hγ : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 2 * t) ((fun _ : ℝ => (2 : ℝ)) t) t := by
    intro t _
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hInt : IntervalIntegrable
      (fun t => inner ℝ ((fun _ : ℝ => (-3 : ℝ)) ((fun t : ℝ => 2 * t) t))
        ((fun _ : ℝ => (2 : ℝ)) t)) volume (0 : ℝ) 1 := by
    simp only []
    exact intervalIntegrable_const
  have h := EarthScience.conservative_force_work_eq_potential_decrease
    (U := fun x : ℝ => 3 * x) (g := fun _ : ℝ => (3 : ℝ))
    (F := fun _ : ℝ => (-3 : ℝ)) (γ := fun t : ℝ => 2 * t)
    (γ' := fun _ : ℝ => (2 : ℝ)) (a := 0) (b := 1) hF hgrad hγ hInt
  have h2 : ∫ t in (0 : ℝ)..1, inner ℝ (-3 : ℝ) (2 : ℝ)
      = -(3 * (2 * 1) - 3 * (2 * 0)) := h
  rw [h2]
  norm_num

set_option linter.unusedVariables false in
/-- Degenerate interval boundary: work over `[5, 5]` is `0`. -/
example : ∫ t in (5 : ℝ)..5, inner ℝ ((-3 : ℝ)) (2 : ℝ) = 0 := by
  simp
