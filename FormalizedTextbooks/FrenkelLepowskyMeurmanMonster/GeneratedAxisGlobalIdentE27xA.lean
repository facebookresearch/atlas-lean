/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Dense identification E27+ (Fourth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e27VH` (Eighth coset image) with `e27xVW` (Fourth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e27x_partM : triMatF true e27VH e27xVW = ((29 : ℚ) / 8) := by
  rw [triMatF_eq_ZI true e27VH e27xVW (e8SrcMatZ.act e27H) (fourthSrcMatZ.act e27xW)
    (e8SrcMat_act_entryZ e27H) (fourthSrcMat_act_entryZ e27xW), ← e27xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e27x_pairChk : pairChk true (e8SrcMatZ.act e27H) e27VH e27xVW (3 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e27x_partP : pairSumQ true e27VH e27xVW = (3 : ℚ) :=
  pairSumQ_of_chk true e27VH e27xVW (e8SrcMatZ.act e27H) (e8SrcMat_act_entryZ e27H) e27x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e27x_octChk : OctadDense.octSumChk 32 4 true e27TH e27xTW (69632 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e27x_partO : octSumZ 32 true e27VH e27xVW = (69632 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e27VH e27xVW e27TH e27xTW _ rfl rfl e27x_octChk

/-- The packed octad transform applies. -/
theorem e27x_octOk : octPackOk 32 e27VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e27VH e27TH e27xTW _ rfl e27x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
