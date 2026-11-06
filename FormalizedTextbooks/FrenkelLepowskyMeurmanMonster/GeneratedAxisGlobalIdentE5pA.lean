/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5+ (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e5VH` (Eighth coset image) with `e5pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e5p_partM : triMatF true e5VH e5pVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI true e5VH e5pVW (e8SrcMatZ.act e5H) (twelfthSrcMatZ.act e5pW)
    (e8SrcMat_act_entryZ e5H) (twelfthSrcMat_act_entryZ e5pW), ← e5pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e5p_pairChk : pairChk true (e8SrcMatZ.act e5H) e5VH e5pVW (52 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e5p_partP : pairSumQ true e5VH e5pVW = (52 : ℚ) :=
  pairSumQ_of_chk true e5VH e5pVW (e8SrcMatZ.act e5H) (e8SrcMat_act_entryZ e5H) e5p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e5p_octChk : OctadDense.octSumChk 32 4 true e5TH e5pTW (1024000 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e5p_partO : octSumZ 32 true e5VH e5pVW = (1024000 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e5VH e5pVW e5TH e5pTW _ rfl rfl e5p_octChk

/-- The packed octad transform applies. -/
theorem e5p_octOk : octPackOk 32 e5VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e5VH e5TH e5pTW _ rfl e5p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
