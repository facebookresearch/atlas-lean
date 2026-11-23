/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.MonotonePointwiseUniform

open Filter Set Topology
open MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted

-- Raise the value of the identity at the right endpoint of [0, 1] to c n.
-- Positive jumps give discontinuous approximants, and their heights may oscillate.
example (c : ℕ → ℝ) (hc : ∀ n, 1 ≤ c n) (hlim : Tendsto c atTop (𝓝 1)) :
    TendstoUniformly (fun n (x : Icc (0 : ℝ) 1) ↦ if (x : ℝ) = 1 then c n else (x : ℝ))
      Subtype.val atTop := by
  refine (monotone_and_tendstoUniformly_of_monotone_tendsto_continuous 0 1 zero_lt_one
    _ Subtype.val ?_ ?_ continuous_subtype_val).2
  · intro n x y hxy
    by_cases hx : (x : ℝ) = 1
    · have hy : (y : ℝ) = 1 := le_antisymm y.2.2 (hx.ge.trans hxy)
      simp [hx, hy]
    · simp only [ite_eq_right hx]
      split
      · exact x.2.2.trans (hc n)
      · exact hxy
  · intro x
    by_cases hx : (x : ℝ) = 1
    · simpa [hx] using hlim
    · simp [hx]
