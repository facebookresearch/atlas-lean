/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.KCenter
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Points `1` and `-1` on the real line are within `2` via the center `0`. -/
example : dist (1 : ℝ) (-1) ≤ 2 * 1 :=
  dist_le_two_mul_of_le (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])

end
