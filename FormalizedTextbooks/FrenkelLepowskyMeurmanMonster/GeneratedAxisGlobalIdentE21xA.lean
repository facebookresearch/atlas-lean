/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E21+ (Seventh target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e21VH` (Eighth coset image) with `e21xVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e21x_partM : triMatF true e21VH e21xVW = ((385 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true e21VH e21xVW (e8SrcMatZ.act e21H) (srcSeventhMatZ.act e21xW)
    (e8SrcMat_act_entryZ e21H) (srcSeventhMat_act_entryZ e21xW), ← e21xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e21x_pairChk : pairChk true (e8SrcMatZ.act e21H) e21VH e21xVW ((119 : ℚ) / 8) = true := by
  decide +kernel

/-- The pair part. -/
theorem e21x_partP : pairSumQ true e21VH e21xVW = ((119 : ℚ) / 8) :=
  pairSumQ_of_chk true e21VH e21xVW (e8SrcMatZ.act e21H) (e8SrcMat_act_entryZ e21H) e21x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e21x_octChk : OctadDense.octSumChk 32 4 true e21TH e21xTW (263392 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e21x_partO : octSumZ 32 true e21VH e21xVW = (263392 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e21VH e21xVW e21TH e21xTW _ rfl rfl e21x_octChk

/-- The packed octad transform applies. -/
theorem e21x_octOk : octPackOk 32 e21VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e21VH e21TH e21xTW _ rfl e21x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
