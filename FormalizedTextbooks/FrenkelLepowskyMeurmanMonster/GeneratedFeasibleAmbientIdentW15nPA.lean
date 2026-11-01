/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W15- (Twelfth root 15
    to Tenth root 38, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW15n_hok : octPackOk 32 fbW15nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false fbW15nL fbW15nHC fbW15nGC 1010176 rfl fbW15n_oct

/-- The octad part of the pairing. -/
theorem fbW15n_hn : octSumZ 32 false fbW15nL fbW15nW = 1010176 :=
  OctadDense.octSumZ_of_chk 32 4 false fbW15nL fbW15nW fbW15nHC fbW15nGC 1010176 rfl rfl fbW15n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW15n_hm : triMatF false fbW15nL fbW15nW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false fbW15nL fbW15nW (twelfthSrcMatZ.act fbW15nH) (srcTenthMatZ.act fbW15nG)
    (twelfthSrcMat_act_entryZ fbW15nH) (srcTenthMat_act_entryZ fbW15nG), ← MatZ.actF_eq fbW15nH,
    ← MatZ.actF_eq fbW15nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW15n_hp : pairSumQ false fbW15nL fbW15nW = ((41 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI false fbW15nL fbW15nW (twelfthSrcMatZ.act fbW15nH) (twelfthSrcMat_act_entryZ
      fbW15nH),
    ← MatZ.actF_eq fbW15nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
