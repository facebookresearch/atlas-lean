/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E17- (Root8 target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e17VH` (Eighth coset image) with `e17mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e17m_partM : triMatF false e17VH e17mVW = ((49 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e17VH e17mVW (e8SrcMatZ.act e17H) (srcRootEightMatZc.act e17mW)
    (e8SrcMat_act_entryZ e17H) (srcRootEightMat_act_entryZc e17mW), ← e17mPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e17m_pairChk : pairChk false (e8SrcMatZ.act e17H) e17VH e17mVW (52 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e17m_partP : pairSumQ false e17VH e17mVW = (52 : ℚ) :=
  pairSumQ_of_chk false e17VH e17mVW (e8SrcMatZ.act e17H) (e8SrcMat_act_entryZ e17H) e17m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e17m_octChk : OctadDense.octSumChk 64 5 false e17TH e17mTW (1016832 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e17m_partO : octSumZ 64 false e17VH e17mVW = (1016832 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 false e17VH e17mVW e17TH e17mTW _ rfl rfl e17m_octChk

/-- The packed octad transform applies. -/
theorem e17m_octOk : octPackOk 64 e17VH = true :=
  OctadDense.octPackOk_of_chk 64 5 false e17VH e17TH e17mTW _ rfl e17m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
