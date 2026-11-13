/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Spatial interpolation and gridded data

## i. Overview

For normalized interpolation weights over a finite index set summing to `1`, a constant field is
  preserved, and a nonnegative normalized combination stays in the range of the samples. This is
  the first clause of the milestone; the finite Gaussian-process posterior is the existing
  `CSLibExt` Gaussian-process regression and is not duplicated here.

## ii. Key results

- `EarthScience.interpolation_preserves_constant`: constant fields are preserved.
- `EarthScience.interpolation_mem_range`: convex combinations stay in the sample range.

## iii. Table of contents

- A. Normalized interpolation

## iv. References

- `Finset.sum_mul`, `Finset.sum_le_sum` in Mathlib.

## A. Normalized interpolation
-/

@[expose] public section

namespace EarthScience

/-- Normalized interpolation preserves a constant field: if the weights over
a finite index set sum to `1` and every sample equals `c`, the weighted sum
is `c`. -/
theorem interpolation_preserves_constant {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (c : ℝ) (hw : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * c = c := by
  rw [← Finset.sum_mul, hw, one_mul]

/-- A convex (nonnegative, normalized) combination stays in the range of the
samples: if every sample lies in `[lo, hi]`, so does the weighted sum. -/
theorem interpolation_mem_range {ι : Type*} (s : Finset ι)
    (w y : ι → ℝ) (lo hi : ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hw : ∑ i ∈ s, w i = 1) (hy : ∀ i ∈ s, lo ≤ y i ∧ y i ≤ hi) :
    lo ≤ ∑ i ∈ s, w i * y i ∧ ∑ i ∈ s, w i * y i ≤ hi := by
  constructor
  · have hconst : ∑ i ∈ s, w i * lo = lo :=
      interpolation_preserves_constant s w lo hw
    rw [← hconst]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hy i hi).1 (hw0 i hi)
  · have hconst : ∑ i ∈ s, w i * hi = hi :=
      interpolation_preserves_constant s w hi hw
    rw [← hconst]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hy i hi).2 (hw0 i hi)


end EarthScience
