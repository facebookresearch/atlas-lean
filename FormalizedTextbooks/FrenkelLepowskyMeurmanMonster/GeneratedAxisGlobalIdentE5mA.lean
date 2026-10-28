/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5- (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e5VH` (Eighth coset image) with `e5mVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e5m_partM : triMatF false e5VH e5mVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI false e5VH e5mVW (e8SrcMatZ.act e5H) (twelfthSrcMatZ.act e5mW)
    (e8SrcMat_act_entryZ e5H) (twelfthSrcMat_act_entryZ e5mW), ← e5mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e5m_pairChk : pairChk false (e8SrcMatZ.act e5H) e5VH e5mVW (52 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e5m_partP : pairSumQ false e5VH e5mVW = (52 : ℚ) :=
  pairSumQ_of_chk false e5VH e5mVW (e8SrcMatZ.act e5H) (e8SrcMat_act_entryZ e5H) e5m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e5m_octChk : OctadDense.octSumChk 32 4 false e5TH e5mTW (1024000 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e5m_partO : octSumZ 32 false e5VH e5mVW = (1024000 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e5VH e5mVW e5TH e5mTW _ rfl rfl e5m_octChk

/-- The packed octad transform applies. -/
theorem e5m_octOk : octPackOk 32 e5VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e5VH e5TH e5mTW _ rfl e5m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
