/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E21-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e21VH` with `e21VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e21m_partM : triMatF false e21VH e21VM = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e21VH e21VM (e8SrcMatZ.act e21H) (e8SrcMatZ.act e21M)
    (e8SrcMat_act_entryZ e21H) (e8SrcMat_act_entryZ e21M), ← e21PlanM_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e21m_pairChk : pairChk false (e8SrcMatZ.act e21H) e21VH e21VM ((137 : ℚ) / 8) = true := by
  decide +kernel

/-- The pair part. -/
theorem e21m_partP : pairSumQ false e21VH e21VM = ((137 : ℚ) / 8) :=
  pairSumQ_of_chk false e21VH e21VM (e8SrcMatZ.act e21H) (e8SrcMat_act_entryZ e21H) e21m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e21m_octChk : OctadDense.octSumChk 32 4 false e21TH e21TM (263392 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e21m_partO : octSumZ 32 false e21VH e21VM = (263392 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e21VH e21VM e21TH e21TM _ rfl rfl e21m_octChk

/-- The packed octad transform applies. -/
theorem e21m_octOk : octPackOk 32 e21VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e21VH e21TH e21TM _ rfl e21m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
