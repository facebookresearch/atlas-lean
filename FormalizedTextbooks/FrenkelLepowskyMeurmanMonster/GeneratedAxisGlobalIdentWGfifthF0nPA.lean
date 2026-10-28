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

/-! # Factory parts (octad check, matrix, pairs) of the identification Fifth[0]- <-> Fifth[0]-
(record gfifth:F0-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGfifthF0n_hok : octPackOk 32 wGfifthF0nL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGfifthF0n_hm : triMatF false wGfifthF0nL wGfifthF0nW = selfMatQ wGfifthF0nW := by
  rw [triMatF_eq_ZI false wGfifthF0nL wGfifthF0nW (fifthSrcMatZ.act wGfifthF0nH) (fifthSrcMatZ.act
      wGfifthF0nG)
    (fifthSrcMat_act_entry wGfifthF0nH) (fifthSrcMat_act_entry wGfifthF0nG),
    selfMatQ_eq_ZI wGfifthF0nW (fifthSrcMatZ.act wGfifthF0nG) (fifthSrcMat_act_entry wGfifthF0nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGfifthF0n_hp : pairSumQ false wGfifthF0nL wGfifthF0nW = wGfifthF0nW.sden * (selfPairsZ
    wGfifthF0nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGfifthF0nL wGfifthF0nW (fifthSrcMatZ.act wGfifthF0nH)
      (fifthSrcMat_act_entry wGfifthF0nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
