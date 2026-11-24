/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.SchubertRankSchemes

/-!
# Tests for rank counts, length and the Bruhat order on permutations
-/

open MathlibExt.AlgebraicGeometry.SchubertRankSchemes

/-- The reversal of `Fin 3` is the longest permutation, with three inversions. -/
example : length (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 := by decide

example : length (1 : Equiv.Perm (Fin 3)) = 0 := by decide

/-- A simple transposition has length one. -/
example : length (Equiv.swap (0 : Fin 3) 1) = 1 := by decide

/-- `rankCount w p q` counts `i < p` with `w i < q`. -/
example : rankCount (1 : Equiv.Perm (Fin 3)) 2 2 = 2 := by decide

example : rankCount (Fin.revPerm : Equiv.Perm (Fin 3)) 2 2 = 1 := by decide

/-- The identity lies below the reversal, which lies above every simple
transposition, in the Bruhat order. -/
example : bruhatLE (1 : Equiv.Perm (Fin 3)) Fin.revPerm := by unfold bruhatLE; decide

example : bruhatLE (Equiv.swap (0 : Fin 3) 1) Fin.revPerm := by unfold bruhatLE; decide

example : ¬ bruhatLE (Fin.revPerm : Equiv.Perm (Fin 3)) 1 := by unfold bruhatLE; decide

/-- The two simple transpositions of `Fin 3` are incomparable. -/
example : ¬ bruhatLE (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 1 2) := by
  unfold bruhatLE; decide

/-- `w₀ (0 1)` is covered by `w₀`, but `w₀ (0 2) = 1` drops length by three. -/
example : downwardCover (Fin.revPerm : Equiv.Perm (Fin 3)) 0 1 := by
  unfold downwardCover bruhatLE; decide

example : ¬ downwardCover (Fin.revPerm : Equiv.Perm (Fin 3)) 0 2 := by
  unfold downwardCover bruhatLE; decide
