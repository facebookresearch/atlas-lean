/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W15+ (Twelfth root 15
    to Tenth root 38, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW15p_hok : octPackOk 32 fbW15pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbW15pL fbW15pHC fbW15pGC 1010176 rfl fbW15p_oct

/-- The octad part of the pairing. -/
theorem fbW15p_hn : octSumZ 32 true fbW15pL fbW15pW = 1010176 :=
  OctadDense.octSumZ_of_chk 32 4 true fbW15pL fbW15pW fbW15pHC fbW15pGC 1010176 rfl rfl fbW15p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW15p_hm : triMatF true fbW15pL fbW15pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true fbW15pL fbW15pW (twelfthSrcMatZ.act fbW15pH) (srcTenthMatZ.act fbW15pG)
    (twelfthSrcMat_act_entryZ fbW15pH) (srcTenthMat_act_entryZ fbW15pG), ← MatZ.actF_eq fbW15pH,
    ← MatZ.actF_eq fbW15pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW15p_hp : pairSumQ true fbW15pL fbW15pW = ((41 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI true fbW15pL fbW15pW (twelfthSrcMatZ.act fbW15pH) (twelfthSrcMat_act_entryZ
      fbW15pH),
    ← MatZ.actF_eq fbW15pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
