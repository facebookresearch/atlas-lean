/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatData

/-! # Odd terms of the cheap Twelfth source vector, coordinates 0-11

For each coordinate one kernel evaluation of the odd terms of the cheap Twelfth source vector
(read off one column of the packed incoming tensor), compared with the literal table. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `0` agree with the literal table. -/
theorem twelfthOdd_check0 : twLBEq (twOddCol 24 twelfthYXC 0) (twelfthOddLit 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `1` agree with the literal table. -/
theorem twelfthOdd_check1 : twLBEq (twOddCol 24 twelfthYXC 1) (twelfthOddLit 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `2` agree with the literal table. -/
theorem twelfthOdd_check2 : twLBEq (twOddCol 24 twelfthYXC 2) (twelfthOddLit 2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `3` agree with the literal table. -/
theorem twelfthOdd_check3 : twLBEq (twOddCol 24 twelfthYXC 3) (twelfthOddLit 3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `4` agree with the literal table. -/
theorem twelfthOdd_check4 : twLBEq (twOddCol 24 twelfthYXC 4) (twelfthOddLit 4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `5` agree with the literal table. -/
theorem twelfthOdd_check5 : twLBEq (twOddCol 24 twelfthYXC 5) (twelfthOddLit 5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `6` agree with the literal table. -/
theorem twelfthOdd_check6 : twLBEq (twOddCol 24 twelfthYXC 6) (twelfthOddLit 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `7` agree with the literal table. -/
theorem twelfthOdd_check7 : twLBEq (twOddCol 24 twelfthYXC 7) (twelfthOddLit 7) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `8` agree with the literal table. -/
theorem twelfthOdd_check8 : twLBEq (twOddCol 24 twelfthYXC 8) (twelfthOddLit 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `9` agree with the literal table. -/
theorem twelfthOdd_check9 : twLBEq (twOddCol 24 twelfthYXC 9) (twelfthOddLit 9) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `10` agree with the literal table. -/
theorem twelfthOdd_check10 : twLBEq (twOddCol 24 twelfthYXC 10) (twelfthOddLit 10) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `11` agree with the literal table. -/
theorem twelfthOdd_check11 : twLBEq (twOddCol 24 twelfthYXC 11) (twelfthOddLit 11) = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
