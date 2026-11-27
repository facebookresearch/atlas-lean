/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InclExclLikeSumBounds
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.inclExclLikeSum_bounds_summary

-- At the minimum dimension, the two tie conventions realize opposite endpoints.
example :
    inclExclLikeSum round (fun _ : Fin 2 => (1 / 2 : ℝ)) = 1 ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin 2 => (1 / 2 : ℝ)) = -1 := by
  have h := (inclExclLikeSum_bounds_summary (n := 2) (by decide)).2.1
  norm_num at h
  exact ⟨h.2.2.2, h.2.1⟩

-- At three quarters the largest subset in dimension two has displacement exactly one half.
example : inclExclLikeSum Int.ceil (fun _ : Fin 2 => (3 / 4 : ℝ)) = 0 ∧
    inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin 2 => (3 / 4 : ℝ)) = 1 := by
  have h := (inclExclLikeSum_bounds_summary (n := 2) (by decide)).2.2.2
  norm_num at h
  omega

-- The lower perturbation in odd dimension attains the strict upper bound for floor.
example : inclExclLikeSum Int.floor (fun _ : Fin 3 => (7 / 18 : ℝ)) = 1 ∧
    inclExclLikeSum round (fun _ : Fin 3 => (7 / 18 : ℝ)) = -2 := by
  have h := (inclExclLikeSum_bounds_summary (n := 3) (by decide)).2.2.1
  norm_num at h
  omega

-- At the minimum dimension, the ceiling sum lies between zero and one for every tuple.
example (x : Fin 2 → ℝ) :
    0 ≤ inclExclLikeSum Int.ceil x ∧ inclExclLikeSum Int.ceil x ≤ 1 := by
  simpa using (inclExclLikeSum_ceil_extrema (n := 2) (by decide)).1 x

-- The two constant tuples attain the lower and upper endpoints in dimension three.
example : inclExclLikeSum Int.ceil (fun _ : Fin 3 => (11 / 18 : ℝ)) = -1 ∧
    inclExclLikeSum Int.ceil (fun _ : Fin 3 => (1 / 2 : ℝ)) = 2 := by
  have h := (inclExclLikeSum_ceil_extrema (n := 3) (by decide)).2
  norm_num at h
  exact h

end MetaMathlibExt.inclExclLikeSum_bounds_summary
