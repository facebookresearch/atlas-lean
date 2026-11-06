/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E13+ (Tenth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e13VH` (Eighth coset image) with `e13pVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e13p_partM : triMatF true e13VH e13pVW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true e13VH e13pVW (e8SrcMatZ.act e13H) (srcTenthMatZc.act e13pW)
    (e8SrcMat_act_entryZ e13H) (srcTenthMat_act_entryZc e13pW), ← e13pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e13p_pairChk : pairChk true (e8SrcMatZ.act e13H) e13VH e13pVW (71 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e13p_partP : pairSumQ true e13VH e13pVW = (71 : ℚ) :=
  pairSumQ_of_chk true e13VH e13pVW (e8SrcMatZ.act e13H) (e8SrcMat_act_entryZ e13H) e13p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^6`). -/
theorem e13p_octChk : OctadDense.octSumChk 64 6 true e13TH e13pTW (1043456 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e13p_partO : octSumZ 64 true e13VH e13pVW = (1043456 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 6 true e13VH e13pVW e13TH e13pTW _ rfl rfl e13p_octChk

/-- The packed octad transform applies. -/
theorem e13p_octOk : octPackOk 64 e13VH = true :=
  OctadDense.octPackOk_of_chk 64 6 true e13VH e13TH e13pTW _ rfl e13p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
