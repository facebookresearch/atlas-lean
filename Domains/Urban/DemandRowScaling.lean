/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Domains.Urban.DemandRow

/-!
# Demand row scaling

Positive rescaling of a demand weight row leaves the normalized
demand unchanged: distributing an origin total by weights `c * w`
with `c > 0` gives the same row as distributing by `w`. The scale
cancels in the normalization; the positive row sum is the gate
that rejects the all-unreachable (all-zero-weight) row.

## Main results

- `UrbanDemand.normalizedDemand_row_scaling`: invariance of the
  normalized row under positive weight rescaling.
-/

@[expose] public section

namespace UrbanDemand

/-- Positive rescaling of a demand weight row leaves the normalized
demand unchanged: with `c > 0`, distributing origin total `O` by
the weights `c * w j` gives the same row as distributing by `w j`,
provided the unscaled row sum is positive. The scale cancels in
the normalization; reachability (which destinations are in `s`) is
unchanged. -/
theorem normalizedDemand_row_scaling {ι : Type*} (O : ℝ)
    (w : ι → ℝ) (s : Finset ι) (i : ι) {c : ℝ} (hc : 0 < c)
    (hsum : 0 < ∑ j ∈ s, w j) :
    normalizedDemand O (fun j => c * w j) s i
      = normalizedDemand O w s i := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have hS : (∑ j ∈ s, w j) ≠ 0 := ne_of_gt hsum
  simp only [normalizedDemand, ← Finset.mul_sum]
  rw [mul_left_comm O c (w i), mul_comm c (O * w i),
    mul_comm c (∑ i ∈ s, w i), mul_div_mul_right _ _ hc']

end UrbanDemand
