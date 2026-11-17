/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Acoustic power transmission

## i. Overview

For patches with incident intensities `I`, areas `A`, and transmission
coefficients `tau`, the effective coefficient is total transmitted over
total incident power. Under uniform positive incident intensity it is
the area-weighted average of the coefficients, and coefficient bounds
`0 < tau_i ≤ 1` are inherited by the effective coefficient.

## ii. Key results

- `Acoustics.effectivePowerTransmission_eq_of_uniform`: uniform
  intensity gives the area-weighted average.
- `Acoustics.effectivePowerTransmission_bounds`: bound inheritance.

## iii. Table of contents

- A. Effective transmission

## iv. References

- L. E. Kinsler, A. R. Frey, A. B. Coppens and J. V. Sanders,
  *Fundamentals of Acoustics*, 4th edition, Wiley, 2000.
-/

@[expose] public section

namespace Acoustics

/-! ## A. Effective transmission -/

/-- Effective power transmission coefficient over patches `s`: total
transmitted power over total incident power. -/
noncomputable def effectivePowerTransmission {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) : ℝ :=
  (∑ i ∈ s, I i * A i * tau i) / (∑ i ∈ s, I i * A i)

/-- Under uniform incident intensity `I0 > 0`, the effective coefficient
is the area-weighted average `(∑ i, A i * tau i) / (∑ i, A i)`. -/
theorem effectivePowerTransmission_eq_of_uniform {ι : Type*}
    (I A tau : ι → ℝ) (s : Finset ι) {I0 : ℝ} (hI0 : 0 < I0)
    (hI : ∀ i : ι, i ∈ s → I i = I0)
    (hA : ∀ i : ι, i ∈ s → 0 < A i) (hs : s.Nonempty) :
    effectivePowerTransmission I A tau s
      = (∑ i ∈ s, A i * tau i) / (∑ i ∈ s, A i) := by
  have _ := hA
  have _ := hs
  unfold effectivePowerTransmission
  have hnum : (∑ i ∈ s, I i * A i * tau i) = I0 * (∑ i ∈ s, A i * tau i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hI i hi]
    ring
  have hden : (∑ i ∈ s, I i * A i) = I0 * (∑ i ∈ s, A i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hI i hi]
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hI0.ne'

/-- The effective coefficient inherits the bounds `0 < tau_eff ≤ 1` from
`0 < tau_i ≤ 1` on every patch of positive area, over a nonempty patch
set. -/
theorem effectivePowerTransmission_bounds {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) (hs : s.Nonempty) {I0 : ℝ} (hI0 : 0 < I0)
    (hI : ∀ i : ι, i ∈ s → I i = I0)
    (hA : ∀ i : ι, i ∈ s → 0 < A i)
    (htau : ∀ i : ι, i ∈ s → 0 < tau i ∧ tau i ≤ 1) :
    0 < effectivePowerTransmission I A tau s
      ∧ effectivePowerTransmission I A tau s ≤ 1 := by
  rw [effectivePowerTransmission_eq_of_uniform I A tau s hI0 hI hA hs]
  have hsumA : 0 < ∑ i ∈ s, A i :=
    Finset.sum_pos (fun i hi => hA i hi) hs
  have hnum : 0 < ∑ i ∈ s, A i * tau i :=
    Finset.sum_pos (fun i hi => mul_pos (hA i hi) (htau i hi).1) hs
  have hle : (∑ i ∈ s, A i * tau i) ≤ (∑ i ∈ s, A i) := by
    apply Finset.sum_le_sum
    intro i hi
    calc A i * tau i ≤ A i * 1 :=
            mul_le_mul_of_nonneg_left (htau i hi).2 (le_of_lt (hA i hi))
        _ = A i := mul_one _
  exact ⟨div_pos hnum hsumA, (div_le_one hsumA).mpr hle⟩

end Acoustics
