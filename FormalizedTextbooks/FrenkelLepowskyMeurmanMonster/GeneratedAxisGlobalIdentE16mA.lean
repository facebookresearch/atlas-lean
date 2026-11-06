/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16- (Root8 target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e16VH` (Eighth coset image) with `e16mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e16m_partM : triMatF false e16VH e16mVW = ((49 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e16VH e16mVW (e8SrcMatZ.act e16H) (srcRootEightMatZc.act e16mW)
    (e8SrcMat_act_entryZ e16H) (srcRootEightMat_act_entryZc e16mW), ← e16mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e16m_pairChk : pairChk false (e8SrcMatZ.act e16H) e16VH e16mVW (68 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e16m_partP : pairSumQ false e16VH e16mVW = (68 : ℚ) :=
  pairSumQ_of_chk false e16VH e16mVW (e8SrcMatZ.act e16H) (e8SrcMat_act_entryZ e16H) e16m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e16m_octChk : OctadDense.octSumChk 64 5 false e16TH e16mTW (1012736 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e16m_partO : octSumZ 64 false e16VH e16mVW = (1012736 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 false e16VH e16mVW e16TH e16mTW _ rfl rfl e16m_octChk

/-- The packed octad transform applies. -/
theorem e16m_octOk : octPackOk 64 e16VH = true :=
  OctadDense.octPackOk_of_chk 64 5 false e16VH e16TH e16mTW _ rfl e16m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
