/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSum
public meta import CSLibExt.Computability.Complexity.Karp.SubsetSum

/-! Tests for the SUBSET-SUM encoding and the VERTEX-COVER-to-SUBSET-SUM construction. -/

namespace Cslib.Complexity.Karp.SubsetSumTests

open Cslib.CookLevin Computability

-- Numbers in binary, least significant bit first, each delimited.
#guard encodeSS [5] 2 =
  [true, false, true, true, false] ++ [true, true, true, false, true, true, false]

/-- Brute force: does some sublist of `as` sum to `t`? -/
private def hits (as : List ℕ) (t : ℕ) : Bool := as.sublists.any fun l => l.sum == t

-- The triangle: pairs `(0, 2), (0, 1), (1, 2)` (digits `1, 4, 16`), all edges.
#guard ssNums 3 [true, true, true] = [69, 84, 81, 1, 4, 16]
#guard ssTarget 2 3 [true, true, true] = 170
-- A cover of 2 vertices exists, of 1 does not; the sums agree.
#guard hits (ssNums 3 [true, true, true]) (ssTarget 2 3 [true, true, true])
#guard !hits (ssNums 3 [true, true, true]) (ssTarget 1 3 [true, true, true])
-- A path `0 - 1 - 2` (pair `(0, 2)` absent, its number is 0): vertex 1 alone covers it.
#guard ssNums 3 [false, true, true] = [68, 84, 80, 0, 4, 16]
#guard hits (ssNums 3 [false, true, true]) (ssTarget 1 3 [false, true, true])
#guard !hits (ssNums 3 [false, true, true]) (ssTarget 0 3 [false, true, true])
-- Sweep: every graph on 3 vertices and every `k ≤ 3` matches a brute-force cover search.
#guard (List.range 8).all fun g =>
  let bits := [g % 2 == 1, g / 2 % 2 == 1, g / 4 % 2 == 1]
  (List.range 4).all fun k =>
    hits (ssNums 3 bits) (ssTarget k 3 bits) ==
      (List.range 3).sublists.any fun s => s.length == k &&
        ((pairs 3).zip bits).all fun pb => !pb.2 || pb.1.1 ∈ s || pb.1.2 ∈ s

-- The bit-string reduction: valid instances, a wrong bit count, an unparsable input.
#guard reduceSS (encodeKG 2 3 [true, true, true]) = encodeSS [69, 84, 81, 1, 4, 16] 170
#guard reduceSS (encodeKG 2 3 [true, true]) = noSS
#guard reduceSS [true] = noSS
#guard !hits [] 1

end Cslib.Complexity.Karp.SubsetSumTests
