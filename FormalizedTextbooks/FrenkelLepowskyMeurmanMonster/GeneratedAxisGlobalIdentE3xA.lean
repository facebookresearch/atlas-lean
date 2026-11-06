/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E3+ (Sixth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e3VH` (Eighth coset image) with `e3xVW` (Sixth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e3x_partM : triMatF true e3VH e3xVW = ((497 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true e3VH e3xVW (e8SrcMatZ.act e3H) (sixthSrcMatZ.act e3xW)
    (e8SrcMat_act_entryZ e3H) (sixthSrcMat_act_entryZ e3xW), ← e3xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e3x_pairChk : pairChk true (e8SrcMatZ.act e3H) e3VH e3xVW ((87 : ℚ) / 8) = true := by
  decide +kernel

/-- The pair part. -/
theorem e3x_partP : pairSumQ true e3VH e3xVW = ((87 : ℚ) / 8) :=
  pairSumQ_of_chk true e3VH e3xVW (e8SrcMatZ.act e3H) (e8SrcMat_act_entryZ e3H) e3x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e3x_octChk : OctadDense.octSumChk 64 5 true e3TH e3xTW (257248 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e3x_partO : octSumZ 64 true e3VH e3xVW = (257248 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 true e3VH e3xVW e3TH e3xTW _ rfl rfl e3x_octChk

/-- The packed octad transform applies. -/
theorem e3x_octOk : octPackOk 64 e3VH = true :=
  OctadDense.octPackOk_of_chk 64 5 true e3VH e3TH e3xTW _ rfl e3x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
