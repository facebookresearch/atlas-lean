/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E6-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e6VH` with `e6VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e6m_partM : triMatF false e6VH e6VM = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e6VH e6VM (e8SrcMatZ.act e6H) (e8SrcMatZ.act e6M)
    (e8SrcMat_act_entryZ e6H) (e8SrcMat_act_entryZ e6M), ← e6PlanM_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e6m_pairChk : pairChk false (e8SrcMatZ.act e6H) e6VH e6VM (15 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e6m_partP : pairSumQ false e6VH e6VM = (15 : ℚ) :=
  pairSumQ_of_chk false e6VH e6VM (e8SrcMatZ.act e6H) (e8SrcMat_act_entryZ e6H) e6m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e6m_octChk : OctadDense.octSumChk 32 4 false e6TH e6TM (258816 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e6m_partO : octSumZ 32 false e6VH e6VM = (258816 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e6VH e6VM e6TH e6TM _ rfl rfl e6m_octChk

/-- The packed octad transform applies. -/
theorem e6m_octOk : octPackOk 32 e6VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e6VH e6TH e6TM _ rfl e6m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
