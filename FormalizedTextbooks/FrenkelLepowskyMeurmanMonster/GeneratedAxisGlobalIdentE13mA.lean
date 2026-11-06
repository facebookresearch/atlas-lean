/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E13- (Seventh target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e13VH` (Eighth coset image) with `e13mVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e13m_partM : triMatF false e13VH e13mVW = ((385 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false e13VH e13mVW (e8SrcMatZ.act e13H) (srcSeventhMatZ.act e13mW)
    (e8SrcMat_act_entryZ e13H) (srcSeventhMat_act_entryZ e13mW), ← e13mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e13m_pairChk : pairChk false (e8SrcMatZ.act e13H) e13VH e13mVW ((51 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e13m_partP : pairSumQ false e13VH e13mVW = ((51 : ℚ) / 4) :=
  pairSumQ_of_chk false e13VH e13mVW (e8SrcMatZ.act e13H) (e8SrcMat_act_entryZ e13H) e13m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e13m_octChk : OctadDense.octSumChk 32 4 false e13TH e13mTW (260864 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e13m_partO : octSumZ 32 false e13VH e13mVW = (260864 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e13VH e13mVW e13TH e13mTW _ rfl rfl e13m_octChk

/-- The packed octad transform applies. -/
theorem e13m_octOk : octPackOk 32 e13VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e13VH e13TH e13mTW _ rfl e13m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
