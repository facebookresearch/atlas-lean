/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions

open MetaMathlibExt

-- At the meter threshold the third arrival fails, even though the fourth can park.
example : meteredOutcome 2 2 [0, 0, 0, 0] = [some 0, some 1, none, some 0] := by decide

example : meteredParkingCount 2 3 2 = 0 := by decide

-- Reducing the meter by one or removing one car allows successful preferences.
example : meteredParkingCount 1 3 2 = 4 := by decide

example : meteredParkingCount 2 2 2 = 3 := by decide

-- With no spots the empty preference list is the only successful one.
example : meteredParkingCount 0 1 0 = 0 ∧ meteredParkingCount 0 0 0 = 1 := by decide
