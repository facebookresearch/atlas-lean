/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatData

/-! # Octad terms of the cheap Twelfth source vector, first half

The octad Fourier blocks of the cheap Twelfth source vector are evaluated in separate kernel checks
(consecutive ranges of `70` octads of the octad list), each compared with the corresponding range of
the literal octad table. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Octads `0` to `69` of the octad list. -/
theorem twelfthOct_check0 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 0).take 70)))
      ((twelfthOctLit.drop 0).take 2176) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `70` to `139` of the octad list. -/
theorem twelfthOct_check1 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 70).take 70)))
      ((twelfthOctLit.drop 2176).take 2816) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `140` to `209` of the octad list. -/
theorem twelfthOct_check2 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 140).take 70)))
      ((twelfthOctLit.drop 4992).take 2688) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `210` to `279` of the octad list. -/
theorem twelfthOct_check3 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 210).take 70)))
      ((twelfthOctLit.drop 7680).take 2880) = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
