/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W16+ (Twelfth root 16
    to Tenth root 28, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW16p_hok : octPackOk 32 fbW16pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbW16pL fbW16pHC fbW16pGC 1010176 rfl fbW16p_oct

/-- The octad part of the pairing. -/
theorem fbW16p_hn : octSumZ 32 true fbW16pL fbW16pW = 1010176 :=
  OctadDense.octSumZ_of_chk 32 4 true fbW16pL fbW16pW fbW16pHC fbW16pGC 1010176 rfl rfl fbW16p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW16p_hm : triMatF true fbW16pL fbW16pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true fbW16pL fbW16pW (twelfthSrcMatZ.act fbW16pH) (srcTenthMatZ.act fbW16pG)
    (twelfthSrcMat_act_entryZ fbW16pH) (srcTenthMat_act_entryZ fbW16pG), ← MatZ.actF_eq fbW16pH,
    ← MatZ.actF_eq fbW16pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW16p_hp : pairSumQ true fbW16pL fbW16pW = ((41 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI true fbW16pL fbW16pW (twelfthSrcMatZ.act fbW16pH) (twelfthSrcMat_act_entryZ
      fbW16pH),
    ← MatZ.actF_eq fbW16pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
