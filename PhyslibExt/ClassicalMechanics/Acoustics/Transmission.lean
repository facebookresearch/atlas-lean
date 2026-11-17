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
  unfold effectivePowerTransmission
  have hI0ne : I0 ≠ 0 := ne_of_gt hI0
  have hnum : (∑ i ∈ s, I i * A i * tau i) = I0 * (∑ i ∈ s, A i * tau i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hI i hi]; ring)
  have hden : (∑ i ∈ s, I i * A i) = I0 * (∑ i ∈ s, A i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hI i hi])
  have _hs : s.Nonempty := hs
  have _hA : ∀ i : ι, i ∈ s → 0 < A i := hA
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hI0ne

/-- The effective coefficient inherits the bounds `0 < tau_eff ≤ 1` from
`0 < tau_i ≤ 1` on every patch of positive area and positive incident
intensity (uniformity is not needed), over a nonempty patch set. -/
theorem effectivePowerTransmission_bounds {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) (hs : s.Nonempty)
    (hI : ∀ i : ι, i ∈ s → 0 < I i)
    (hA : ∀ i : ι, i ∈ s → 0 < A i)
    (htau : ∀ i : ι, i ∈ s → 0 < tau i ∧ tau i ≤ 1) :
    0 < effectivePowerTransmission I A tau s
      ∧ effectivePowerTransmission I A tau s ≤ 1 := by
  unfold effectivePowerTransmission
  have hwpos : ∀ i ∈ s, 0 < I i * A i :=
    fun i hi => mul_pos (hI i hi) (hA i hi)
  have hDpos : 0 < ∑ i ∈ s, I i * A i := Finset.sum_pos hwpos hs
  have hNpos : 0 < ∑ i ∈ s, I i * A i * tau i :=
    Finset.sum_pos (fun i hi => mul_pos (hwpos i hi) (htau i hi).1) hs
  have hNleD : (∑ i ∈ s, I i * A i * tau i) ≤ (∑ i ∈ s, I i * A i) :=
    Finset.sum_le_sum (fun i hi =>
      mul_le_of_le_one_right (le_of_lt (hwpos i hi)) (htau i hi).2)
  exact ⟨div_pos hNpos hDpos, (div_le_one hDpos).mpr hNleD⟩

end Acoustics
