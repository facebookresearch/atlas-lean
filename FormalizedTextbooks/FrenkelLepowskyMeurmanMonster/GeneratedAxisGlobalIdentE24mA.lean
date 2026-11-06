/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E24- (Seventh target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e24VH` (Eighth coset image) with `e24mVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e24m_partM : triMatF false e24VH e24mVW = ((385 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false e24VH e24mVW (e8SrcMatZ.act e24H) (srcSeventhMatZ.act e24mW)
    (e8SrcMat_act_entryZ e24H) (srcSeventhMat_act_entryZ e24mW), ← e24mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e24m_pairChk : pairChk false (e8SrcMatZ.act e24H) e24VH e24mVW ((163 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e24m_partP : pairSumQ false e24VH e24mVW = ((163 : ℚ) / 4) :=
  pairSumQ_of_chk false e24VH e24mVW (e8SrcMatZ.act e24H) (e8SrcMat_act_entryZ e24H) e24m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e24m_octChk : OctadDense.octSumChk 32 4 false e24TH e24mTW (261888 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e24m_partO : octSumZ 32 false e24VH e24mVW = (261888 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e24VH e24mVW e24TH e24mTW _ rfl rfl e24m_octChk

/-- The packed octad transform applies. -/
theorem e24m_octOk : octPackOk 32 e24VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e24VH e24TH e24mTW _ rfl e24m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
