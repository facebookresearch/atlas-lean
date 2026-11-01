/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E27-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e27VH` with `e27VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e27m_partM : triMatF false e27VH e27VM = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI false e27VH e27VM (e8SrcMatZ.act e27H) (e8SrcMatZ.act e27M)
    (e8SrcMat_act_entryZ e27H) (e8SrcMat_act_entryZ e27M), ← e27PlanM_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e27m_pairChk : pairChk false (e8SrcMatZ.act e27H) e27VH e27VM (34 : ℚ) = true := by
  decide +kernel

/-- The pair part. -/
theorem e27m_partP : pairSumQ false e27VH e27VM = (34 : ℚ) :=
  pairSumQ_of_chk false e27VH e27VM (e8SrcMatZ.act e27H) (e8SrcMat_act_entryZ e27H) e27m_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e27m_octChk : OctadDense.octSumChk 32 4 false e27TH e27TM (278528 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e27m_partO : octSumZ 32 false e27VH e27VM = (278528 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e27VH e27VM e27TH e27TM _ rfl rfl e27m_octChk

/-- The packed octad transform applies. -/
theorem e27m_octOk : octPackOk 32 e27VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e27VH e27TH e27TM _ rfl e27m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
