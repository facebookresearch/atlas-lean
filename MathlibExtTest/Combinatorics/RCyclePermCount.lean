/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RCyclePermCount

/-! # Tests for counting permutations with all cycles of length $r$ -/

namespace MetaMathlibExt.RCyclePermCountTest

example (r n : ℕ) (hr : 2 ≤ r) :
    (Finset.univ.filter (IsRCyclePerm r n)).card =
      if r ∣ n then n.factorial / (r ^ (n / r) * (n / r).factorial) else 0 :=
  card_rCyclePerm (r := r) (n := n) (hr := hr)

-- The empty permutation satisfies the orbit condition vacuously.
example (r : ℕ) (hr : 2 ≤ r) : (Finset.univ.filter (IsRCyclePerm r 0)).card = 1 := by
  simpa using card_rCyclePerm (r := r) (n := 0) (hr := hr)

-- A transposition on three points leaves a fixed point, so none is counted.
example : (Finset.univ.filter (IsRCyclePerm 2 3)).card = 0 :=
  (card_rCyclePerm (r := 2) (n := 3) (hr := by decide)).trans (by decide)

-- There are three pairings of four points into two transpositions.
example : (Finset.univ.filter (IsRCyclePerm 2 4)).card = 3 :=
  (card_rCyclePerm (r := 2) (n := 4) (hr := by decide)).trans (by decide)

end MetaMathlibExt.RCyclePermCountTest
