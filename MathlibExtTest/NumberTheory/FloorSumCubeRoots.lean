/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FloorSumCubeRoots

open MathlibExt.NumberTheory.OeisConjecturesWanted

-- The thousand-term sum has floor 7504; no numerical approximation of cube roots is used.
example : Nat.floor (∑ i ∈ Finset.Icc (1 : ℕ) 1000, (i : ℝ) ^ (1 / 3 : ℝ)) = 7504 := by
  have h := floor_sum_cbrt 1 (by decide)
  rw [show (10 : ℕ) ^ (3 * 1) = 1000 by decide,
    show (3 * 10 ^ (4 * 1) / 4 + 5 * 10 ^ (1 - 1) - 1 : ℕ) = 7504 by decide] at h
  exact h
