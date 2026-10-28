/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W17+ (Twelfth root 17
    to Tenth root 44, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW17p_hok : octPackOk 32 fbW17pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbW17pL fbW17pHC fbW17pGC 1009152 rfl fbW17p_oct

/-- The octad part of the pairing. -/
theorem fbW17p_hn : octSumZ 32 true fbW17pL fbW17pW = 1009152 :=
  OctadDense.octSumZ_of_chk 32 4 true fbW17pL fbW17pW fbW17pHC fbW17pGC 1009152 rfl rfl fbW17p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW17p_hm : triMatF true fbW17pL fbW17pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true fbW17pL fbW17pW (twelfthSrcMatZ.act fbW17pH) (srcTenthMatZ.act fbW17pG)
    (twelfthSrcMat_act_entryZ fbW17pH) (srcTenthMat_act_entryZ fbW17pG), ← MatZ.actF_eq fbW17pH,
    ← MatZ.actF_eq fbW17pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW17p_hp : pairSumQ true fbW17pL fbW17pW = ((45 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI true fbW17pL fbW17pW (twelfthSrcMatZ.act fbW17pH) (twelfthSrcMat_act_entryZ
      fbW17pH),
    ← MatZ.actF_eq fbW17pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
