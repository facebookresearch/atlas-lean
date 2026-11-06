/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E11- (Twelfth target): matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e11VH` (Eighth coset image) with `e11xVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e11x_partM : triMatF false e11VH e11xVW = ((91 : ℚ) / 32) := by
  rw [triMatF_eq_ZI false e11VH e11xVW (e8SrcMatZ.act e11H) (twelfthSrcMatZ.act e11xW)
    (e8SrcMat_act_entryZ e11H) (twelfthSrcMat_act_entryZ e11xW), ← e11xPlanW_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e11x_pairChk : pairChk false (e8SrcMatZ.act e11H) e11VH e11xVW (63 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e11x_partP : pairSumQ false e11VH e11xVW = (63 : ℚ) :=
  pairSumQ_of_chk false e11VH e11xVW (e8SrcMatZ.act e11H) (e8SrcMat_act_entryZ e11H) e11x_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e11x_octChk : OctadDense.octSumChk 32 4 false e11TH e11xTW (1029376 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e11x_partO : octSumZ 32 false e11VH e11xVW = (1029376 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e11VH e11xVW e11TH e11xTW _ rfl rfl e11x_octChk

/-- The packed octad transform applies. -/
theorem e11x_octOk : octPackOk 32 e11VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e11VH e11TH e11xTW _ rfl e11x_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
