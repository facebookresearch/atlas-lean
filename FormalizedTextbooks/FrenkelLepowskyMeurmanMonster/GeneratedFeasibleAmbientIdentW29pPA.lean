/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W29+ (Twelfth root 29
    to Tenth root 48, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW29p_hok : octPackOk 32 fbW29pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbW29pL fbW29pHC fbW29pGC 1007488 rfl fbW29p_oct

/-- The octad part of the pairing. -/
theorem fbW29p_hn : octSumZ 32 true fbW29pL fbW29pW = 1007488 :=
  OctadDense.octSumZ_of_chk 32 4 true fbW29pL fbW29pW fbW29pHC fbW29pGC 1007488 rfl rfl fbW29p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW29p_hm : triMatF true fbW29pL fbW29pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true fbW29pL fbW29pW (twelfthSrcMatZ.act fbW29pH) (srcTenthMatZ.act fbW29pG)
    (twelfthSrcMat_act_entryZ fbW29pH) (srcTenthMat_act_entryZ fbW29pG), ← MatZ.actF_eq fbW29pH,
    ← MatZ.actF_eq fbW29pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW29p_hp : pairSumQ true fbW29pL fbW29pW = ((135 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true fbW29pL fbW29pW (twelfthSrcMatZ.act fbW29pH) (twelfthSrcMat_act_entryZ
      fbW29pH),
    ← MatZ.actF_eq fbW29pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
