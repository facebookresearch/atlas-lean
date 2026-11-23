/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Combination
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

- `Acoustics.effectivePowerTransmission_eq`: the center-mass
  coefficient is the transmitted/incident power quotient.
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

/-- Effective power transmission coefficient over patches `s`: total
transmitted over total incident power, as the `Finset.centerMass`
weighted average of the coefficients with weights `I i * A i`. -/
noncomputable def effectivePowerTransmission {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) : ℝ :=
  s.centerMass (fun i => I i * A i) tau

/-- The center-mass coefficient is the transmitted/incident power
quotient, unconditionally (both sides are zero when the total incident
weight is zero). -/
theorem effectivePowerTransmission_eq {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) :
    effectivePowerTransmission I A tau s
      = (∑ i ∈ s, I i * A i * tau i) / (∑ i ∈ s, I i * A i) := by
  simp only [effectivePowerTransmission, Finset.centerMass, smul_eq_mul,
    div_eq_inv_mul]

/-- Under uniform incident intensity `I0 > 0`, the effective coefficient
is the area-weighted average `(∑ i, A i * tau i) / (∑ i, A i)`. No
positivity of areas or nonemptiness is needed for this identity. -/
theorem effectivePowerTransmission_eq_of_uniform {ι : Type*}
    (I A tau : ι → ℝ) (s : Finset ι) {I0 : ℝ} (hI0 : 0 < I0)
    (hI : ∀ i : ι, i ∈ s → I i = I0) :
    effectivePowerTransmission I A tau s
      = (∑ i ∈ s, A i * tau i) / (∑ i ∈ s, A i) := by
  rw [effectivePowerTransmission_eq]
  have hI0ne : I0 ≠ 0 := ne_of_gt hI0
  have hnum : (∑ i ∈ s, I i * A i * tau i) = I0 * (∑ i ∈ s, A i * tau i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hI i hi]; ring)
  have hden : (∑ i ∈ s, I i * A i) = I0 * (∑ i ∈ s, A i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hI i hi])
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hI0ne

/-- The effective coefficient inherits the bounds `0 < tau_eff ≤ 1` from
`0 < tau_i ≤ 1` on every patch of positive area and positive incident
intensity, over a nonempty patch set. -/
theorem effectivePowerTransmission_bounds {ι : Type*} (I A tau : ι → ℝ)
    (s : Finset ι) (hs : s.Nonempty)
    (hI : ∀ i : ι, i ∈ s → 0 < I i)
    (hA : ∀ i : ι, i ∈ s → 0 < A i)
    (htau : ∀ i : ι, i ∈ s → 0 < tau i ∧ tau i ≤ 1) :
    0 < effectivePowerTransmission I A tau s
      ∧ effectivePowerTransmission I A tau s ≤ 1 := by
  rw [effectivePowerTransmission_eq]
  have hw : ∀ i ∈ s, 0 < I i * A i := fun i hi => mul_pos (hI i hi) (hA i hi)
  have hden : 0 < ∑ i ∈ s, I i * A i := Finset.sum_pos hw hs
  have hnum : 0 < ∑ i ∈ s, I i * A i * tau i := by
    apply Finset.sum_pos _ hs
    intro i hi
    exact mul_pos (hw i hi) (htau i hi).1
  refine ⟨div_pos hnum hden, ?_⟩
  rw [div_le_one hden]
  apply Finset.sum_le_sum
  intro i hi
  calc I i * A i * tau i ≤ (I i * A i) * 1 :=
        mul_le_mul_of_nonneg_left (htau i hi).2 (le_of_lt (hw i hi))
    _ = I i * A i := mul_one _

end Acoustics
