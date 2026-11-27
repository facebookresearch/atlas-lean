/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RegularOverpartition

namespace MetaMathlibExt

-- The empty overpartition is the only overpartition of zero, also for `ℓ = 0`.
example : regularOverpartitionCount 0 0 = 1 :=
  regularOverpartitionCount_zero 0

example : regularOverpartitionCount 5 0 = 1 :=
  regularOverpartitionCount_zero 5

-- The overpartitions of one are `1` and its overlined copy.
example : regularOverpartitionCount 3 1 = 2 :=
  regularOverpartitionCount_one 3 (hℓ := by decide)

-- `ℓ = 3`, `n = 0`, `j = 1`: the count of `7` is divisible by `4` (it is `36`).
example : Nat.ModEq 4 (regularOverpartitionCount 3 7) 0 :=
  regularOverpartition_mod_four_progression 3 0 1 (hℓ := by decide) (hj := by decide)

-- `ℓ = 7`, `n = 1`, `j = 0`, where `(ℓ - 3) / 4 = 1`.
example : Nat.ModEq 4 (regularOverpartitionCount 7 31) 0 :=
  regularOverpartition_mod_four_progression 7 1 0 (hℓ := by decide) (hj := by decide)

-- The whole progression `28 n + 3` for `ℓ = 7`.
example (n : ℕ) : Nat.ModEq 4 (regularOverpartitionCount 7 (28 * n + 3)) 0 := by
  have h := regularOverpartition_mod_four_progression 7 n 0 (hℓ := by decide) (hj := by decide)
  rwa [show 4 * 7 * n + 4 * 0 + 3 = 28 * n + 3 by omega] at h

-- `ℓ = 11`: every residue `j` other than `(11 - 3) / 4 = 2` modulo `11`.
example (n j : ℕ) (hj : j % 11 ≠ 2) :
    Nat.ModEq 4 (regularOverpartitionCount 11 (44 * n + 4 * j + 3)) 0 := by
  have h := regularOverpartition_mod_four_progression 11 n j (hℓ := by decide)
    (hj := fun h => hj (by simpa [Nat.ModEq] using h))
  rwa [show 4 * 11 * n + 4 * j + 3 = 44 * n + 4 * j + 3 by omega] at h

end MetaMathlibExt
