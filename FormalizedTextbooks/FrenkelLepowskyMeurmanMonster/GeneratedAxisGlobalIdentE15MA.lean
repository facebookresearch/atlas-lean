/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E15-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e15VH` with `e15VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e15m_partM : triMatF false e15VH e15VM = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e15VH e15VM (e8SrcMatZ.act e15H) (e8SrcMatZ.act e15M)
    (e8SrcMat_act_entryZ e15H) (e8SrcMat_act_entryZ e15M), ← e15PlanM_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e15m_pairChk : pairChk false (e8SrcMatZ.act e15H) e15VH e15VM ((79 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e15m_partP : pairSumQ false e15VH e15VM = ((79 : ℚ) / 4) :=
  pairSumQ_of_chk false e15VH e15VM (e8SrcMatZ.act e15H) (e8SrcMat_act_entryZ e15H) e15m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e15m_octChk : OctadDense.octSumChk 32 4 false e15TH e15TM (255552 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e15m_partO : octSumZ 32 false e15VH e15VM = (255552 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e15VH e15VM e15TH e15TM _ rfl rfl e15m_octChk

/-- The packed octad transform applies. -/
theorem e15m_octOk : octPackOk 32 e15VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e15VH e15TH e15TM _ rfl e15m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
