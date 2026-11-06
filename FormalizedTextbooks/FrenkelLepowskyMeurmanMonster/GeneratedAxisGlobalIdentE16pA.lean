/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16+ (Root8 target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e16VH` (Eighth coset image) with `e16pVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e16p_partM : triMatF true e16VH e16pVW = ((49 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e16VH e16pVW (e8SrcMatZ.act e16H) (srcRootEightMatZc.act e16pW)
    (e8SrcMat_act_entryZ e16H) (srcRootEightMat_act_entryZc e16pW), ← e16pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e16p_pairChk : pairChk true (e8SrcMatZ.act e16H) e16VH e16pVW (68 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e16p_partP : pairSumQ true e16VH e16pVW = (68 : ℚ) :=
  pairSumQ_of_chk true e16VH e16pVW (e8SrcMatZ.act e16H) (e8SrcMat_act_entryZ e16H) e16p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e16p_octChk : OctadDense.octSumChk 64 5 true e16TH e16pTW (1012736 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e16p_partO : octSumZ 64 true e16VH e16pVW = (1012736 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 true e16VH e16pVW e16TH e16pTW _ rfl rfl e16p_octChk

/-- The packed octad transform applies. -/
theorem e16p_octOk : octPackOk 64 e16VH = true :=
  OctadDense.octPackOk_of_chk 64 5 true e16VH e16TH e16pTW _ rfl e16p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
