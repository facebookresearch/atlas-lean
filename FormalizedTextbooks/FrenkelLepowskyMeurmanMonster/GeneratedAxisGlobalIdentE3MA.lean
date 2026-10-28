/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E3-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e3VH` with `e3VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e3m_partM : triMatF false e3VH e3VM = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e3VH e3VM (e8SrcMatZ.act e3H) (e8SrcMatZ.act e3M)
    (e8SrcMat_act_entryZ e3H) (e8SrcMat_act_entryZ e3M), ← e3PlanM_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e3m_pairChk : pairChk false (e8SrcMatZ.act e3H) e3VH e3VM ((329 : ℚ) / 8) = true := by
  decide +kernel

/-- The pair part. -/
theorem e3m_partP : pairSumQ false e3VH e3VM = ((329 : ℚ) / 8) :=
  pairSumQ_of_chk false e3VH e3VM (e8SrcMatZ.act e3H) (e8SrcMat_act_entryZ e3H) e3m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e3m_octChk : OctadDense.octSumChk 32 4 false e3TH e3TM (257248 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e3m_partO : octSumZ 32 false e3VH e3VM = (257248 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e3VH e3VM e3TH e3TM _ rfl rfl e3m_octChk

/-- The packed octad transform applies. -/
theorem e3m_octOk : octPackOk 32 e3VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e3VH e3TH e3TM _ rfl e3m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
