/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.RootsFilter
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Quantum.RootsFilter

/-- For `ζ = 1`, every term is `1` and the sum is the period. -/
example : (∑ j ∈ Finset.range 3, ((1 : ℂ) ^ 2) ^ j) = 3 := by
  rw [roots_filter (1 : ℂ) (by norm_num) (by norm_num) 2, ite_eq_left (by norm_num)]
  norm_num

/-- For `ζ = -1`, `k = 2` and `m = 1`, the terms `1` and `-1` cancel and the sum is `0`. -/
example : (∑ j ∈ Finset.range 2, ((-1 : ℂ) ^ 1) ^ j) = 0 := by
  rw [roots_filter (-1 : ℂ) (by norm_num) (by norm_num) 1, ite_eq_right (by norm_num)]

/-- `ζ = i` is a 4th root of unity and `ζ ^ 2 = -1 ≠ 1`, so the four terms
`1, -1, 1, -1` cancel even though `ζ ^ 2` is not a primitive 4th root. -/
example : (∑ j ∈ Finset.range 4, (Complex.I ^ 2) ^ j) = 0 := by
  rw [roots_filter Complex.I (by norm_num) Complex.I_pow_four 2,
    ite_eq_right (by rw [Complex.I_sq]; norm_num)]

end
