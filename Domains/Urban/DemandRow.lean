/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Singly constrained demand rows

## i. Overview

A singly constrained demand row distributes an origin total `O` over
destinations in proportion to nonnegative weights: `T i = O * w i /
∑ j, w j`. Entries are nonnegative and the row total is exactly `O`
when the weight sum is positive.

## ii. Key results

- `UrbanDemand.normalizedDemand_nonneg`: entries are nonnegative.
- `UrbanDemand.normalizedDemand_sum`: the row total is exact.

## iii. Table of contents

- A. Normalized demand rows

## iv. References

- A. G. Wilson, *Entropy in Urban and Regional Modelling*, Pion, 1970
  (spatial interaction models).
-/

@[expose] public section

namespace UrbanDemand

/-! ## A. Normalized demand rows -/

/-- Singly constrained demand row entry: origin total `O` distributed in proportion to the weights
`w` over destination set `s`: `T i = O * w i / ∑ j in s, w j`. The definition imposes no sign
condition on `O` or `w`; the value is `0` when `∑ j in s, w j = 0`. -/
noncomputable def normalizedDemand {ι : Type*} (O : ℝ) (w : ι → ℝ) (s : Finset ι)
    (i : ι) : ℝ :=
  O * w i / ∑ j ∈ s, w j

/-- With `O ≥ 0` and nonnegative weights of positive sum on `s`, each normalized row entry at a
destination of `s` is nonnegative. -/
theorem normalizedDemand_nonneg {ι : Type*} (O : ℝ) (w : ι → ℝ) (s : Finset ι)
    (hO : 0 ≤ O) (hw : ∀ i : ι, i ∈ s → 0 ≤ w i) (hsum : 0 < ∑ j ∈ s, w j)
    {i : ι} (hi : i ∈ s) :
    0 ≤ normalizedDemand O w s i := by
  unfold normalizedDemand
  exact div_nonneg (mul_nonneg hO (hw i hi)) hsum.le

/-- With `O ≥ 0` and nonnegative weights of positive sum on `s`, the normalized row has exact total
`O`. -/
theorem normalizedDemand_sum {ι : Type*} (O : ℝ) (w : ι → ℝ) (s : Finset ι)
    (hO : 0 ≤ O) (hw : ∀ i : ι, i ∈ s → 0 ≤ w i) (hsum : 0 < ∑ j ∈ s, w j) :
    ∑ i ∈ s, normalizedDemand O w s i = O := by
  have _ : 0 ≤ O := hO
  have _ : ∀ i : ι, i ∈ s → 0 ≤ w i := hw
  have hS : (∑ j ∈ s, w j) ≠ 0 := ne_of_gt hsum
  unfold normalizedDemand
  rw [← Finset.sum_div, ← Finset.mul_sum]
  exact mul_div_cancel_right₀ _ hS

end UrbanDemand
