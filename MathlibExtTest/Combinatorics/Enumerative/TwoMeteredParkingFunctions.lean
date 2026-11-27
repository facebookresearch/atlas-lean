/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TwoMeteredParkingFunctions

open MetaMathlibExt

-- The two cars cannot both park with zero spots or one spot.
example : meteredParkingCount 1 2 0 = 0 ∧ meteredParkingCount 1 2 1 = 0 := by decide

-- Count directly from the parking rule at the minimum positive meter.
example : meteredParkingCount 1 2 3 = 8 := by decide

-- The same formula applies with a longer meter.
example : meteredParkingCount 4 2 3 = 8 :=
  meteredParkingCount_two (by decide) 3
