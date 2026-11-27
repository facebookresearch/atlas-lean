/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrithoffPrecolumns

/-! # Tests for the precolumns of the Trithoff array -/

namespace MetaMathlibExt.trithoff_precolumns

-- The word 011 represents 3 with a leading zero and has a nonzero seed correction.
example :
    let wall := (11 : ℤ) - 6 - 3
    let seed := (6 : ℤ) - 3 - wall
    wall = 2 ∧ seed = 1 ∧ 3 - wall - seed = 0 :=
  trithoff_precolumns [] 0 1 3 (by unfold IsTribonacciRepr; decide)

-- The word 1101 represents 12. Both its prefix and its digit b contribute to the pre-seed.
example :
    let wall := (41 : ℤ) - 22 - 12
    let seed := (22 : ℤ) - 12 - wall
    wall = 7 ∧ seed = 3 ∧ 12 - wall - seed = 2 :=
  trithoff_precolumns [1] 1 0 12 (by unfold IsTribonacciRepr; decide)

-- Three consecutive ones have a Tribonacci value but fail the representation predicate.
example : tribonacciValue [1, 1, 1] = 7 ∧ ¬ IsTribonacciRepr [1, 1, 1] 7 := by
  unfold IsTribonacciRepr tribonacciValue
  decide

end MetaMathlibExt.trithoff_precolumns
