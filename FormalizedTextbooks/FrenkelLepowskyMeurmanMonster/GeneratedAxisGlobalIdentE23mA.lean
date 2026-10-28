/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E23- (Root8 target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e23VH` (Eighth coset image) with `e23mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e23m_partM : triMatF false e23VH e23mVW = ((49 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e23VH e23mVW (e8SrcMatZ.act e23H) (srcRootEightMatZc.act e23mW)
    (e8SrcMat_act_entryZ e23H) (srcRootEightMat_act_entryZc e23mW), ← e23mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e23m_pairChk : pairChk false (e8SrcMatZ.act e23H) e23VH e23mVW ((89 : ℚ) / 2) = true := by
  decide +kernel

/-- The pair part. -/
theorem e23m_partP : pairSumQ false e23VH e23mVW = ((89 : ℚ) / 2) :=
  pairSumQ_of_chk false e23VH e23mVW (e8SrcMatZ.act e23H) (e8SrcMat_act_entryZ e23H) e23m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e23m_octChk : OctadDense.octSumChk 64 5 false e23TH e23mTW (1014656 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e23m_partO : octSumZ 64 false e23VH e23mVW = (1014656 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 false e23VH e23mVW e23TH e23mTW _ rfl rfl e23m_octChk

/-- The packed octad transform applies. -/
theorem e23m_octOk : octPackOk 64 e23VH = true :=
  OctadDense.octPackOk_of_chk 64 5 false e23VH e23TH e23mTW _ rfl e23m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
