/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E29- (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e29VH` (Eighth coset image) with `e29mVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e29m_partM : triMatF false e29VH e29mVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI false e29VH e29mVW (e8SrcMatZ.act e29H) (twelfthSrcMatZ.act e29mW)
    (e8SrcMat_act_entryZ e29H) (twelfthSrcMat_act_entryZ e29mW), ← e29mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e29m_pairChk : pairChk false (e8SrcMatZ.act e29H) e29VH e29mVW (53 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e29m_partP : pairSumQ false e29VH e29mVW = (53 : ℚ) :=
  pairSumQ_of_chk false e29VH e29mVW (e8SrcMatZ.act e29H) (e8SrcMat_act_entryZ e29H) e29m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e29m_octChk : OctadDense.octSumChk 32 4 false e29TH e29mTW (1023744 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e29m_partO : octSumZ 32 false e29VH e29mVW = (1023744 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e29VH e29mVW e29TH e29mTW _ rfl rfl e29m_octChk

/-- The packed octad transform applies. -/
theorem e29m_octOk : octPackOk 32 e29VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e29VH e29TH e29mTW _ rfl e29m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
