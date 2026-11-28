/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema` -/

namespace MathlibExtTest.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema

open MetaMathlibExt

-- At the minimum dimension the bounds say `-1 ≤ g₁ x ≤ 0`.
example (x : Fin 2 → ℝ) :
    -1 ≤ inclExclLikeSum Int.floor x ∧ inclExclLikeSum Int.floor x ≤ 0 := by
  have h := (inclExclLikeSum_floor_extrema (n := 2) (by decide)).1 x
  norm_num at h
  exact h

-- At the minimum dimension the minimum `-1` is attained at `(1 / 2, 1 / 2)`.
example : inclExclLikeSum Int.floor (fun _ : Fin 2 => (1 / 2 : ℝ)) = -1 := by
  have h := (inclExclLikeSum_floor_extrema (n := 2) (by decide)).2.1
  norm_num at h
  exact h

-- At the minimum dimension the maximum `0` is attained at `(1 / 4, 1 / 4)`.
example : inclExclLikeSum Int.floor (fun _ : Fin 2 => (1 / 4 : ℝ)) = 0 := by
  have h := (inclExclLikeSum_floor_extrema (n := 2) (by decide)).2.2
  norm_num at h
  exact h

end MathlibExtTest.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema
