/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.OneMeteredTwoSpots

open MetaMathlibExt

namespace MathlibExtTest.OneMeteredTwoSpots

-- A singleton `1` can be followed by a new lace, and there can be more cars than spots.
example : IsMeteredParkingFunction (n := 2) 1 ![1, 0, 0, 0] := by
  rw [isMeteredParkingFunction_one_two_iff_lace (by decide)]
  decide

-- A lucky `1` blocks a second `1`. The later successful car cannot repair the failure.
example : ¬ IsMeteredParkingFunction (n := 2) 1 ![1, 1, 0] := by
  rw [isMeteredParkingFunction_one_two_iff_lace (by decide)]
  decide

-- A bumped `0` also blocks a `1`.
example : ¬ IsMeteredParkingFunction (n := 2) 1 ![0, 0, 1] := by
  rw [isMeteredParkingFunction_one_two_iff_lace (by decide)]
  decide

example : ¬ IsMeteredParkingFunction (n := 2) 1 ![0, 0, 1] := by decide

end MathlibExtTest.OneMeteredTwoSpots
