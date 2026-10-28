/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W18+ (Twelfth root 18
    to Tenth root 36, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW18p_hok : octPackOk 32 fbW18pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbW18pL fbW18pHC fbW18pGC 1018752 rfl fbW18p_oct

/-- The octad part of the pairing. -/
theorem fbW18p_hn : octSumZ 32 true fbW18pL fbW18pW = 1018752 :=
  OctadDense.octSumZ_of_chk 32 4 true fbW18pL fbW18pW fbW18pHC fbW18pGC 1018752 rfl rfl fbW18p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW18p_hm : triMatF true fbW18pL fbW18pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true fbW18pL fbW18pW (twelfthSrcMatZ.act fbW18pH) (srcTenthMatZ.act fbW18pG)
    (twelfthSrcMat_act_entryZ fbW18pH) (srcTenthMat_act_entryZ fbW18pG), ← MatZ.actF_eq fbW18pH,
    ← MatZ.actF_eq fbW18pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW18p_hp : pairSumQ true fbW18pL fbW18pW = ((111 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true fbW18pL fbW18pW (twelfthSrcMatZ.act fbW18pH) (twelfthSrcMat_act_entryZ
      fbW18pH),
    ← MatZ.actF_eq fbW18pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
