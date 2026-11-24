/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.KNaplesParking

open MetaMathlibExt

-- Even with a long backward search, zero is never an available spot.
example : naplesSpot 2 4 [1, 2] 2 = none := by decide

-- Moving the first car from 5 to 1 makes three later cars park in different spots.
example : naplesPark 5 1 [] [5, 2, 2, 3, 4] = some [4, 3, 1, 2, 5] ∧
    naplesPark 5 1 [1, 2] [2, 3, 4] = some [5, 4, 3, 1, 2] := by decide

example : (naplesPark 5 1 [1, 2] [2, 3, 4]).isSome := by
  apply naplesPark_drop_set_isSome (α := ![5, 2, 2, 3, 4]) (d := [5, 2, 1, 3, 4])
    (i := 2) (l := 0) (q := 1)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro j hj hne
    have : j = 1 := by omega
    subst j
    decide
