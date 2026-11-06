/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth

/-! # Pairing parts (octads, matrix, pairs) of the identification gtenth:T14+ (Tenth root 14 to
    Twelfth root 7, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbT14p_hok : octPackOk 32 fbT14pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true fbT14pL fbT14pHC fbT14pGC 1013888 rfl fbT14p_oct

/-- The octad part of the pairing. -/
theorem fbT14p_hn : octSumZ 32 true fbT14pL fbT14pW = 1013888 :=
  OctadDense.octSumZ_of_chk 32 4 true fbT14pL fbT14pW fbT14pHC fbT14pGC 1013888 rfl rfl fbT14p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbT14p_hm : triMatF true fbT14pL fbT14pW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI true fbT14pL fbT14pW (srcTenthMatZ.act fbT14pH) (twelfthSrcMatZ.act fbT14pG)
    (srcTenthMat_act_entryZ fbT14pH) (twelfthSrcMat_act_entryZ fbT14pG), ← MatZ.actF_eq fbT14pH,
    ← MatZ.actF_eq fbT14pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbT14p_hp : pairSumQ true fbT14pL fbT14pW = ((87 : ℚ) / 2) := by
  rw [pairSumQ_eq_ZI true fbT14pL fbT14pW (srcTenthMatZ.act fbT14pH) (srcTenthMat_act_entryZ
      fbT14pH),
    ← MatZ.actF_eq fbT14pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
