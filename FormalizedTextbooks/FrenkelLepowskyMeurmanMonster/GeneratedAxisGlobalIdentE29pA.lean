/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E29+ (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e29VH` (Eighth coset image) with `e29pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e29p_partM : triMatF true e29VH e29pVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI true e29VH e29pVW (e8SrcMatZ.act e29H) (twelfthSrcMatZ.act e29pW)
    (e8SrcMat_act_entryZ e29H) (twelfthSrcMat_act_entryZ e29pW), ← e29pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e29p_pairChk : pairChk true (e8SrcMatZ.act e29H) e29VH e29pVW (53 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e29p_partP : pairSumQ true e29VH e29pVW = (53 : ℚ) :=
  pairSumQ_of_chk true e29VH e29pVW (e8SrcMatZ.act e29H) (e8SrcMat_act_entryZ e29H) e29p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e29p_octChk : OctadDense.octSumChk 32 4 true e29TH e29pTW (1023744 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e29p_partO : octSumZ 32 true e29VH e29pVW = (1023744 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e29VH e29pVW e29TH e29pTW _ rfl rfl e29p_octChk

/-- The packed octad transform applies. -/
theorem e29p_octOk : octPackOk 32 e29VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e29VH e29TH e29pTW _ rfl e29p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
