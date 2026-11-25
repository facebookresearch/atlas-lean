/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MeteredParkingLowerBound

open MetaMathlibExt

-- With a zero meter every spot is available to each arriving car.
example (m n : ℕ) : n ^ m ≤ meteredParkingCount 0 m n := by
  simpa using pow_sub_le_meteredParkingCount 0 m n

-- Even when subtraction truncates to zero, the empty preference list contributes one.
example (t n : ℕ) : 1 ≤ meteredParkingCount t 0 n := by
  simpa using pow_sub_le_meteredParkingCount t 0 n

-- For four spots and a meter of length two, preference one is the last guaranteed choice.
example : meteredOutcome 2 4 [1, 1, 1, 1] = [some 1, some 2, some 3, some 1] ∧
    meteredOutcome 2 4 [2, 2, 2] = [some 2, some 3, none] := by decide
