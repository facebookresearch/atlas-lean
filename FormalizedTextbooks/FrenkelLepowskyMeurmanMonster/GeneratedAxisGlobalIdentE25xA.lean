/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Dense identification E25- (Fifth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e25VH` (Eighth coset image) with `e25xVW` (Fifth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e25x_partM : triMatF false e25VH e25xVW = (3 : ℚ) := by
  rw [triMatF_eq_ZI false e25VH e25xVW (e8SrcMatZ.act e25H) (fifthSrcMatZ.act e25xW)
    (e8SrcMat_act_entryZ e25H) (fifthSrcMat_act_entry e25xW), ← e25xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e25x_pairChk : pairChk false (e8SrcMatZ.act e25H) e25VH e25xVW (8 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e25x_partP : pairSumQ false e25VH e25xVW = (8 : ℚ) :=
  pairSumQ_of_chk false e25VH e25xVW (e8SrcMatZ.act e25H) (e8SrcMat_act_entryZ e25H) e25x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e25x_octChk : OctadDense.octSumChk 32 4 false e25TH e25xTW (124928 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e25x_partO : octSumZ 32 false e25VH e25xVW = (124928 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e25VH e25xVW e25TH e25xTW _ rfl rfl e25x_octChk

/-- The packed octad transform applies. -/
theorem e25x_octOk : octPackOk 32 e25VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e25VH e25TH e25xTW _ rfl e25x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
