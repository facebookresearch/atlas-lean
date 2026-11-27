/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.FinsetSum
import Mathlib.Analysis.Convex.Mul

namespace MathlibExt.Analysis.Convex.FinsetSum

-- `x ↦ ∑_{i < n} (x - i)²` is convex on `ℝ`.
example (n : ℕ) : ConvexOn ℝ Set.univ (fun x : ℝ => ∑ i ∈ Finset.range n, (x - i) ^ 2) := by
  refine convexOn_finset_sum convex_univ _ fun i _ => ?_
  have h := ((show Even 2 by norm_num).convexOn_pow (𝕜 := ℝ)).comp_affineMap
    (AffineMap.const ℝ ℝ (-(i : ℝ)) + AffineMap.id ℝ ℝ)
  refine h.congr fun x _ => ?_
  simp [sub_eq_neg_add]

-- The empty sum is the constant `0`, which is convex.
example : ConvexOn ℝ Set.univ (fun x : ℝ => ∑ i ∈ (∅ : Finset ℕ), x * i) :=
  convexOn_finset_sum convex_univ ∅ (by simp)

end MathlibExt.Analysis.Convex.FinsetSum
