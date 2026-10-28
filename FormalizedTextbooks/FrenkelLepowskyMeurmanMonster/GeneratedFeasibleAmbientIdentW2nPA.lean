/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W2- (Twelfth root 2 to
    Tenth root 8, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW2n_hok : octPackOk 32 fbW2nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false fbW2nL fbW2nHC fbW2nGC 1009664 rfl fbW2n_oct

/-- The octad part of the pairing. -/
theorem fbW2n_hn : octSumZ 32 false fbW2nL fbW2nW = 1009664 :=
  OctadDense.octSumZ_of_chk 32 4 false fbW2nL fbW2nW fbW2nHC fbW2nGC 1009664 rfl rfl fbW2n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW2n_hm : triMatF false fbW2nL fbW2nW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false fbW2nL fbW2nW (twelfthSrcMatZ.act fbW2nH) (srcTenthMatZ.act fbW2nG)
    (twelfthSrcMat_act_entryZ fbW2nH) (srcTenthMat_act_entryZ fbW2nG), ← MatZ.actF_eq fbW2nH,
    ← MatZ.actF_eq fbW2nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW2n_hp : pairSumQ false fbW2nL fbW2nW = ((43 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI false fbW2nL fbW2nW (twelfthSrcMatZ.act fbW2nH) (twelfthSrcMat_act_entryZ
      fbW2nH),
    ← MatZ.actF_eq fbW2nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
