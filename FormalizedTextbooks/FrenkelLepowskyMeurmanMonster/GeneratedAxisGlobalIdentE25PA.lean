/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E25+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e25VH` with `e25VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e25p_partM : triMatF true e25VH e25VP = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e25VH e25VP (e8SrcMatZ.act e25H) (e8SrcMatZ.act e25P)
    (e8SrcMat_act_entryZ e25H) (e8SrcMat_act_entryZ e25P), ← e25PlanP_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e25p_pairChk : pairChk true (e8SrcMatZ.act e25H) e25VH e25VP (18 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e25p_partP : pairSumQ true e25VH e25VP = (18 : ℚ) :=
  pairSumQ_of_chk true e25VH e25VP (e8SrcMatZ.act e25H) (e8SrcMat_act_entryZ e25H) e25p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e25p_octChk : OctadDense.octSumChk 32 4 true e25TH e25TP (249856 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e25p_partO : octSumZ 32 true e25VH e25VP = (249856 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e25VH e25VP e25TH e25TP _ rfl rfl e25p_octChk

/-- The packed octad transform applies. -/
theorem e25p_octOk : octPackOk 32 e25VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e25VH e25TH e25TP _ rfl e25p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
