/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorization

/-!
# Tests for the Lehmer function
-/

open MetaMathlibExt

-- The upper endpoint is attained in every admissible length.
example (r : ℕ) : lehmerKappa (List.replicate r 2) = 2 ^ r - 1 := by
  norm_num [lehmerKappa, List.map_replicate, List.prod_replicate]

-- At length one, the strict lower bound fails throughout the domain.
example (x : ℝ) (hx : 2 ≤ x) : lehmerKappa [x] = 1 := by
  have h : x - 1 ≠ 0 := by linarith
  simp [lehmerKappa, h]

-- Increasing the middle entry of an unsorted list with repeated entries.
example (y : ℝ) (hy : 2 < y) : lehmerKappa [3, y, 2] < lehmerKappa [3, 2, 2] := by
  have h := lehmerKappa_antitone_bounds 3 (by decide) [3, 2, 2] rfl (by norm_num)
  exact h.2 1 (by decide) y hy
