/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted

/-! # Tests for `MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted` -/

namespace MathlibExtTest.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted

open MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted

-- The toggle order on two points is the single arc `(0, 1)`.
example : toggleOrder 2 = [((0 : Fin 2), (1 : Fin 2))] := by decide

-- The toggle order on three points lists the length-one arcs first, then `(0, 2)`.
example : toggleOrder 3 =
    [((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3)),
      ((0 : Fin 3), (2 : Fin 3))] := by decide

-- The empty arc set on three points has three blocks.
example : blockCount (∅ : ArcSet 3) = 3 := by decide

-- The block count is `n - #arcs`: two arcs on three points leave one block.
example : blockCount ({((0 : Fin 3), (2 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
    ArcSet 3) = 1 := by decide

-- The empty arc set is noncrossing.
example : IsNoncrossingArcSet (∅ : ArcSet 3) := by
  unfold IsNoncrossingArcSet
  decide

-- Adjacent arcs sharing a point are noncrossing.
example : IsNoncrossingArcSet ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
    ArcSet 3) := by
  unfold IsNoncrossingArcSet
  decide

-- Two arcs sharing a right endpoint are not noncrossing.
example : ¬ IsNoncrossingArcSet ({((0 : Fin 3), (2 : Fin 3)),
    ((1 : Fin 3), (2 : Fin 3))} : ArcSet 3) := by
  unfold IsNoncrossingArcSet
  decide

-- Two crossing arcs are not noncrossing.
example : ¬ IsNoncrossingArcSet ({((0 : Fin 4), (2 : Fin 4)),
    ((1 : Fin 4), (3 : Fin 4))} : ArcSet 4) := by
  unfold IsNoncrossingArcSet
  decide

-- Toggling at `(0, 1)` adds that arc to the empty arc set on two points.
example : toggle ((0 : Fin 2), (1 : Fin 2)) (∅ : ArcSet 2) =
    {((0 : Fin 2), (1 : Fin 2))} := by
  have hnc : IsNoncrossingArcSet ({((0 : Fin 2), (1 : Fin 2))} : ArcSet 2) := by
    unfold IsNoncrossingArcSet
    decide
  unfold toggle
  simp [hnc]

-- Toggling at an arc present in an arc set removes it.
example : toggle ((0 : Fin 2), (1 : Fin 2))
    ({((0 : Fin 2), (1 : Fin 2))} : ArcSet 2) = ∅ := by
  unfold toggle
  simp

end MathlibExtTest.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted
