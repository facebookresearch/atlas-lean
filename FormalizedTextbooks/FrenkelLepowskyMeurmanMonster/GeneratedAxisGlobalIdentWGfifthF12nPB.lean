/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octads, odd short terms) of the identification Fifth[12]- <-> Fourth[2]-
(record gfifth:F12-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGfifthF12n_hn : wGfifthF12nL.sden * (octSumZ 32 false wGfifthF12nL wGfifthF12nW : ℚ) / 8 =
    wGfifthF12nW.sden * (selfOctP wGfifthF12nW : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short part equals the odd self part of the target. -/
theorem wGfifthF12n_ha : (oddWZ 64 false wGfifthF12nHX wGfifthF12nW : ℚ) / (2 * ((tensorWordDenAll
    wGfifthF12nH : ℚ) * 1)) =
    wGfifthF12nW.sden * (selfOddP wGfifthF12nW : ℚ) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
