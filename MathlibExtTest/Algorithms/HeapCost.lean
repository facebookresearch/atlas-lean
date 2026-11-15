/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.HeapCost

@[expose] public section

/-- At `n = 0` the charged cost is zero. -/
example : (∑ h ∈ Finset.range 0, ((0 : ℝ) / 2 ^ (h + 1)) * h) ≤ 0 :=
  build_heap_cost_bound 0

/-- The weight sum at `k = 2` is `1 / 4 ≤ 1`. -/
example : (∑ h ∈ Finset.range 2, (h : ℝ) / 2 ^ (h + 1)) ≤ 1 :=
  geom_weight_sum_le 2

end
