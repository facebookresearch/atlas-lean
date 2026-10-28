/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W10- (Twelfth root 10
    to Tenth root 51, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW10n_hok : octPackOk 32 fbW10nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false fbW10nL fbW10nHC fbW10nGC 1037824 rfl fbW10n_oct

/-- The octad part of the pairing. -/
theorem fbW10n_hn : octSumZ 32 false fbW10nL fbW10nW = 1037824 :=
  OctadDense.octSumZ_of_chk 32 4 false fbW10nL fbW10nW fbW10nHC fbW10nGC 1037824 rfl rfl fbW10n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW10n_hm : triMatF false fbW10nL fbW10nW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false fbW10nL fbW10nW (twelfthSrcMatZ.act fbW10nH) (srcTenthMatZ.act fbW10nG)
    (twelfthSrcMat_act_entryZ fbW10nH) (srcTenthMat_act_entryZ fbW10nG), ← MatZ.actF_eq fbW10nH,
    ← MatZ.actF_eq fbW10nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW10n_hp : pairSumQ false fbW10nL fbW10nW = ((61 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI false fbW10nL fbW10nW (twelfthSrcMatZ.act fbW10nH) (twelfthSrcMat_act_entryZ
      fbW10nH),
    ← MatZ.actF_eq fbW10nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
