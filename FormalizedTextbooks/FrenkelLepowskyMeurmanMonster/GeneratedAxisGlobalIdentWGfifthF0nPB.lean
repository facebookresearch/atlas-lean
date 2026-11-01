/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Factory parts (octads, odd short terms) of the identification Fifth[0]- <-> Fifth[0]-
(record gfifth:F0-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGfifthF0n_hn : wGfifthF0nL.sden * (octSumZ 32 false wGfifthF0nL wGfifthF0nW : ℚ) / 8 =
    wGfifthF0nW.sden * (selfOctP wGfifthF0nW : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short part equals the odd self part of the target. -/
theorem wGfifthF0n_ha : (oddWZ 64 false wGfifthF0nHX wGfifthF0nW : ℚ) / (2 * ((tensorWordDenAll
    wGfifthF0nH : ℚ) * 1)) =
    wGfifthF0nW.sden * (selfOddP wGfifthF0nW : ℚ) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
