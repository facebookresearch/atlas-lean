/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E17+ (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e17VH` (Eighth coset image) with `e17pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e17p_partM : triMatF true e17VH e17pVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI true e17VH e17pVW (e8SrcMatZ.act e17H) (twelfthSrcMatZ.act e17pW)
    (e8SrcMat_act_entryZ e17H) (twelfthSrcMat_act_entryZ e17pW), ← e17pPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e17p_pairChk : pairChk true (e8SrcMatZ.act e17H) e17VH e17pVW (80 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e17p_partP : pairSumQ true e17VH e17pVW = (80 : ℚ) :=
  pairSumQ_of_chk true e17VH e17pVW (e8SrcMatZ.act e17H) (e8SrcMat_act_entryZ e17H) e17p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e17p_octChk : OctadDense.octSumChk 32 4 true e17TH e17pTW (1016832 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e17p_partO : octSumZ 32 true e17VH e17pVW = (1016832 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e17VH e17pVW e17TH e17pTW _ rfl rfl e17p_octChk

/-- The packed octad transform applies. -/
theorem e17p_octOk : octPackOk 32 e17VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e17VH e17TH e17pTW _ rfl e17p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
