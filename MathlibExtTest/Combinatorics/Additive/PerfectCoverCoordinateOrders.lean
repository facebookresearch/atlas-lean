/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Additive.PerfectCoverCoordinateOrders

open MetaMathlibExt MetaMathlibExt.PerfectSubsetSumCover

private def cover : Fin 4 → ZMod 2 × ZMod (2 ^ 2) := ![(1, 0), (0, 1), (0, 2), (1, 0)]

-- The repeated entry makes this a 2-cover, not a set enumerated without repetition.
private theorem cover_perfect : IsPerfectMCover 2 cover := by decide

example : ∃ i, addOrderOf (cover i).2 = 2 :=
  exists_snd_addOrderOf_of_isPerfectMCover (r := 1) (by decide) cover_perfect 1 (by decide) (by decide)

example : ∃ i, addOrderOf (cover i).2 = 4 :=
  exists_snd_addOrderOf_of_isPerfectMCover (r := 1) (by decide) cover_perfect 2 (by decide) (by decide)

-- At n = 0 the range of requested orders is empty, even for an empty family.
example : ∀ j : ℕ, 1 ≤ j → j ≤ 0 → ∃ _i : Fin 0, addOrderOf (0 : ZMod (2 ^ 0)) = 2 ^ j :=
  exists_snd_addOrderOf_of_isPerfectMCover (r := 0) (n := 0)
    (H := ZMod 1) (s := fun _ : Fin 0 => (0, 0)) (m := 1) (by decide) (by decide)
