/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares

namespace Nat

example : threeSquareRepresentationCount 0 = 1 := by decide

example : threeSquareRepresentationCount 1 = 6 := by decide

example : threeSquareRepresentationCount 7 = 0 :=
  threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven 7 (by decide) (by decide)

example : threeSquareRepresentationCount 4 = threeSquareRepresentationCount 1 :=
  threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four 4
    (by decide) (by decide)

example : hurwitzClassNumber 0 = -1 / 12 := by decide +kernel

example : hurwitzClassNumber 1 = 0 := by decide +kernel

example : hurwitzClassNumber 2 = 0 := by decide +kernel

example : hurwitzClassNumber 3 = 1 / 3 := by decide +kernel

example : hurwitzClassNumber 4 = 1 / 2 := by decide +kernel

-- The ordinary form (1, 0, 3) and the imprimitive hexagonal form (2, 2, 2).
example : hurwitzClassNumber 12 = 4 / 3 := by decide +kernel

-- The boundary form (2, 1, 2) is counted, not its negative-b partner.
example : hurwitzClassNumber 15 = 2 := by decide +kernel

-- The strict interior forms (2, 1, 3) and (2, -1, 3) are distinct proper classes.
example : hurwitzClassNumber 23 = 3 := by decide +kernel

#print axioms Nat.hurwitzClassNumber
#print axioms Nat.threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven
#print axioms Nat.threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four

end Nat
