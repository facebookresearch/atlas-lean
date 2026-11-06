/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E35- (Root8 target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e35VH` (Eighth coset image) with `e35xVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e35x_partM : triMatF false e35VH e35xVW = ((49 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e35VH e35xVW (e8SrcMatZ.act e35H) (srcRootEightMatZc.act e35xW)
    (e8SrcMat_act_entryZ e35H) (srcRootEightMat_act_entryZc e35xW), ← e35xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e35x_pairChk : pairChk false (e8SrcMatZ.act e35H) e35VH e35xVW (57 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e35x_partP : pairSumQ false e35VH e35xVW = (57 : ℚ) :=
  pairSumQ_of_chk false e35VH e35xVW (e8SrcMatZ.act e35H) (e8SrcMat_act_entryZ e35H) e35x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `64`, field bound `2^5`). -/
theorem e35x_octChk : OctadDense.octSumChk 64 5 false e35TH e35xTW (1023744 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e35x_partO : octSumZ 64 false e35VH e35xVW = (1023744 : ℤ) :=
  OctadDense.octSumZ_of_chk 64 5 false e35VH e35xVW e35TH e35xTW _ rfl rfl e35x_octChk

/-- The packed octad transform applies. -/
theorem e35x_octOk : octPackOk 64 e35VH = true :=
  OctadDense.octPackOk_of_chk 64 5 false e35VH e35TH e35xTW _ rfl e35x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
