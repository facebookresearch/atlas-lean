/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the identification gtwelfth:W16- (Twelfth root 16
    to Tenth root 28, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fbW16n_hok : octPackOk 32 fbW16nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false fbW16nL fbW16nHC fbW16nGC 1010176 rfl fbW16n_oct

/-- The octad part of the pairing. -/
theorem fbW16n_hn : octSumZ 32 false fbW16nL fbW16nW = 1010176 :=
  OctadDense.octSumZ_of_chk 32 4 false fbW16nL fbW16nW fbW16nHC fbW16nGC 1010176 rfl rfl fbW16n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fbW16n_hm : triMatF false fbW16nL fbW16nW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false fbW16nL fbW16nW (twelfthSrcMatZ.act fbW16nH) (srcTenthMatZ.act fbW16nG)
    (twelfthSrcMat_act_entryZ fbW16nH) (srcTenthMat_act_entryZ fbW16nG), ← MatZ.actF_eq fbW16nH,
    ← MatZ.actF_eq fbW16nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem fbW16n_hp : pairSumQ false fbW16nL fbW16nW = ((41 : ℚ) / 4) := by
  rw [pairSumQ_eq_ZI false fbW16nL fbW16nW (twelfthSrcMatZ.act fbW16nH) (twelfthSrcMat_act_entryZ
      fbW16nH),
    ← MatZ.actF_eq fbW16nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
