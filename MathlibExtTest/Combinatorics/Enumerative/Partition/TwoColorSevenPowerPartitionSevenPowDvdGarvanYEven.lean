/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartitionSevenPowDvdGarvanYEven

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartitionSevenPowDvdGarvanYEven

-- The first entry of the first even vector is `7`, computed directly.
example : MetaMathlibExt.garvanYEven 1 1 1 = 7 := by decide

-- At `k = 1`, `β = 0`, `j = 1` the first vector entry is divisible by `7`.
example : 7 ∣ MetaMathlibExt.garvanYEven 1 1 1 := by
  have h := (MetaMathlibExt.seven_pow_dvd_garvanYEven 1 0 1 (by decide) (by decide)).1
  simpa using h

-- At `k = 1`, `β = 0`, `j = 1` the second vector entry is divisible by `7 ^ 2`.
example : 7 ^ 2 ∣ MetaMathlibExt.garvanYEven 1 2 1 := by
  have h := (MetaMathlibExt.seven_pow_dvd_garvanYEven 1 0 1 (by decide) (by decide)).2
  simpa using h

-- At `j = 2` the floor term contributes one more factor of seven.
example : 7 ^ 2 ∣ MetaMathlibExt.garvanYEven 1 1 2 := by
  have h := (MetaMathlibExt.seven_pow_dvd_garvanYEven 1 0 2 (by decide) (by decide)).1
  simpa using h

end MathlibExtTest.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartitionSevenPowDvdGarvanYEven
