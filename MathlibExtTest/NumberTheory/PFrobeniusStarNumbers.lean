/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PFrobeniusStarNumbers

namespace MetaMathlibExt.StarNumber

example : star 0 = 1 := by decide
example : star 1 = 1 := by decide
example : star 2 = 13 := by decide
example : star 3 = 37 := by decide
example : star 4 = 73 := by decide

/-- `gcd (13, 37, 73) = 1`. -/
example : Nat.gcd (Nat.gcd (star 2) (star 3)) (star 4) = 1 :=
  gcd_star_succ_succ 2 (by decide)

#print axioms star
#print axioms gcd_star_succ_succ

end MetaMathlibExt.StarNumber
