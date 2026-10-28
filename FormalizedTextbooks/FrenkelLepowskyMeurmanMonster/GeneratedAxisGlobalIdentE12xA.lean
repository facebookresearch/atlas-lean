/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E12- (Tenth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e12VH` (Eighth coset image) with `e12xVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e12x_partM : triMatF false e12VH e12xVW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false e12VH e12xVW (e8SrcMatZ.act e12H) (srcTenthMatZc.act e12xW)
    (e8SrcMat_act_entryZ e12H) (srcTenthMat_act_entryZc e12xW), ← e12xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e12x_pairChk : pairChk false (e8SrcMatZ.act e12H) e12VH e12xVW ((127 : ℚ) / 2) = true := by
  decide +kernel

/-- The pair part. -/
theorem e12x_partP : pairSumQ false e12VH e12xVW = ((127 : ℚ) / 2) :=
  pairSumQ_of_chk false e12VH e12xVW (e8SrcMatZ.act e12H) (e8SrcMat_act_entryZ e12H) e12x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e12x_octChk : OctadDense.octSumChk 64 5 false e12TH e12xTW (1024896 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e12x_partO : octSumZ 64 false e12VH e12xVW = (1024896 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 false e12VH e12xVW e12TH e12xTW _ rfl rfl e12x_octChk

/-- The packed octad transform applies. -/
theorem e12x_octOk : octPackOk 64 e12VH = true :=
  OctadDense.octPackOk_of_chk 64 5 false e12VH e12TH e12xTW _ rfl e12x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
