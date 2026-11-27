/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.PerfectCoverPrescribedOddCoordinates

open MetaMathlibExt MetaMathlibExt.PerfectSubsetSumCover

-- With a trivial first factor, only the last coordinate contributes an odd entry.
example : ∃ S : Finset (ZMod 1 × ZMod 8),
    IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = 1 :=
  exists_isPerfectCover_card_odd (m := 0) (n := 3) (by decide) (by decide) (by decide) (by decide)

-- An interior count for a noncyclic first factor and last coordinates modulo four.
example : ∃ S : Finset ((ZMod 4 × ZMod 2) × ZMod 4),
    IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = 2 :=
  exists_isPerfectCover_card_odd (m := 3) (n := 2) (by decide) (by decide) (by decide) (by decide)

-- At k = m + 1, and with n = 1, every entry can have an odd last coordinate.
example : ∃ S : Finset (ZMod 4 × ZMod 2),
    IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = 3 :=
  exists_isPerfectCover_card_odd (m := 2) (n := 1) (by decide) (by decide) (by decide) (by decide)

-- Check the maximal case directly on a concrete cover, without the existence theorem.
example : let S : Finset (ZMod 4 × ZMod 2) := {(1, 1), (2, 1), (0, 1)}
    IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = 3 := by
  decide
