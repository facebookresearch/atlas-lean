/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.LuckyCars

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- The search starts at the preference, even when a lower spot is free.
example : parkSpots (n := 3) ![1, 1, 0] = ![1, 2, 0] := by decide
example : luckyCount (n := 3) ![1, 1, 0] = 2 := by decide

-- When all spots at or above the preference are occupied, it is returned as the fallback.
example : nextFreeSpot ({1, 2} : Finset (Fin 3)) 1 = 1 := by decide
