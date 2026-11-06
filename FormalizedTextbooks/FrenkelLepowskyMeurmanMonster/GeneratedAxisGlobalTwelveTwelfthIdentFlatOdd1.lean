/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatData

/-! # Odd terms of the cheap Twelfth source vector, coordinates 12-23

For each coordinate one kernel evaluation of the odd terms of the cheap Twelfth source vector
(read off one column of the packed incoming tensor), compared with the literal table. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `12` agree with the literal table. -/
theorem twelfthOdd_check12 : twLBEq (twOddCol 24 twelfthYXC 12) (twelfthOddLit 12) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `13` agree with the literal table. -/
theorem twelfthOdd_check13 : twLBEq (twOddCol 24 twelfthYXC 13) (twelfthOddLit 13) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `14` agree with the literal table. -/
theorem twelfthOdd_check14 : twLBEq (twOddCol 24 twelfthYXC 14) (twelfthOddLit 14) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `15` agree with the literal table. -/
theorem twelfthOdd_check15 : twLBEq (twOddCol 24 twelfthYXC 15) (twelfthOddLit 15) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `16` agree with the literal table. -/
theorem twelfthOdd_check16 : twLBEq (twOddCol 24 twelfthYXC 16) (twelfthOddLit 16) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `17` agree with the literal table. -/
theorem twelfthOdd_check17 : twLBEq (twOddCol 24 twelfthYXC 17) (twelfthOddLit 17) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `18` agree with the literal table. -/
theorem twelfthOdd_check18 : twLBEq (twOddCol 24 twelfthYXC 18) (twelfthOddLit 18) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `19` agree with the literal table. -/
theorem twelfthOdd_check19 : twLBEq (twOddCol 24 twelfthYXC 19) (twelfthOddLit 19) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `20` agree with the literal table. -/
theorem twelfthOdd_check20 : twLBEq (twOddCol 24 twelfthYXC 20) (twelfthOddLit 20) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `21` agree with the literal table. -/
theorem twelfthOdd_check21 : twLBEq (twOddCol 24 twelfthYXC 21) (twelfthOddLit 21) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `22` agree with the literal table. -/
theorem twelfthOdd_check22 : twLBEq (twOddCol 24 twelfthYXC 22) (twelfthOddLit 22) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of coordinate `23` agree with the literal table. -/
theorem twelfthOdd_check23 : twLBEq (twOddCol 24 twelfthYXC 23) (twelfthOddLit 23) = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
