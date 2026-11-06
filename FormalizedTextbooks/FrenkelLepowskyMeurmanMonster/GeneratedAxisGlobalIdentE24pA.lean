/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E24+ (Sixth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e24VH` (Eighth coset image) with `e24pVW` (Sixth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e24p_partM : triMatF true e24VH e24pVW = ((497 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true e24VH e24pVW (e8SrcMatZ.act e24H) (sixthSrcMatZ.act e24pW)
    (e8SrcMat_act_entryZ e24H) (sixthSrcMat_act_entryZ e24pW), ← e24pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e24p_pairChk : pairChk true (e8SrcMatZ.act e24H) e24VH e24pVW ((51 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e24p_partP : pairSumQ true e24VH e24pVW = ((51 : ℚ) / 4) :=
  pairSumQ_of_chk true e24VH e24pVW (e8SrcMatZ.act e24H) (e8SrcMat_act_entryZ e24H) e24p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e24p_octChk : OctadDense.octSumChk 64 5 true e24TH e24pTW (261888 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e24p_partO : octSumZ 64 true e24VH e24pVW = (261888 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 true e24VH e24pVW e24TH e24pTW _ rfl rfl e24p_octChk

/-- The packed octad transform applies. -/
theorem e24p_octOk : octPackOk 64 e24VH = true :=
  OctadDense.octPackOk_of_chk 64 5 true e24VH e24TH e24pTW _ rfl e24p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
