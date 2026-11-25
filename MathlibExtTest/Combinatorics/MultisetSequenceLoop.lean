/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

meta import MathlibExt.Combinatorics.MultisetSequenceLoop

/-! # Tests for multiset inventory sequences -/

namespace MathlibExt.Combinatorics.MultisetSequenceLoopWanted.Tests

#guard step ([], []) = ([], [])

#guard step ([2], [2]) = ([2], [2])

-- A new key comes from the second row, and the two occurrences of 7 combine.
#guard step ([2, 7], [7, 1]) = ([1, 2, 7], [1, 1, 2])

-- A cycle on fourteen keys exercises counts with more than one decimal digit.
private meta def twoCycle : List ℕ × List ℕ :=
  ((List.range 14).map Nat.succ, [11, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1])

#guard step twoCycle ≠ twoCycle ∧ step^[2] twoCycle = twoCycle

-- The period-three family from Cain and Enin, Theorem 5.3, with the free keys 6 and 7.
private meta def threeCycle : List ℕ × List ℕ :=
  ([1, 2, 3, 4, 5, 6, 7], [4, 4, 1, 1, 2, 1, 1])

#guard step threeCycle ≠ threeCycle ∧ step^[2] threeCycle ≠ threeCycle ∧
    step^[3] threeCycle = threeCycle

end MathlibExt.Combinatorics.MultisetSequenceLoopWanted.Tests
