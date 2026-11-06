/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E23+ (Tenth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e23VH` (Eighth coset image) with `e23pVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e23p_partM : triMatF true e23VH e23pVW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true e23VH e23pVW (e8SrcMatZ.act e23H) (srcTenthMatZc.act e23pW)
    (e8SrcMat_act_entryZ e23H) (srcTenthMat_act_entryZc e23pW), ← e23pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e23p_pairChk : pairChk true (e8SrcMatZ.act e23H) e23VH e23pVW ((143 : ℚ) / 2) = true := by
  decide +kernel

/-- The pair part. -/
theorem e23p_partP : pairSumQ true e23VH e23pVW = ((143 : ℚ) / 2) :=
  pairSumQ_of_chk true e23VH e23pVW (e8SrcMatZ.act e23H) (e8SrcMat_act_entryZ e23H) e23p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e23p_octChk : OctadDense.octSumChk 64 5 true e23TH e23pTW (1014656 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e23p_partO : octSumZ 64 true e23VH e23pVW = (1014656 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 true e23VH e23pVW e23TH e23pTW _ rfl rfl e23p_octChk

/-- The packed octad transform applies. -/
theorem e23p_octOk : octPackOk 64 e23VH = true :=
  OctadDense.octPackOk_of_chk 64 5 true e23VH e23TH e23pTW _ rfl e23p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
