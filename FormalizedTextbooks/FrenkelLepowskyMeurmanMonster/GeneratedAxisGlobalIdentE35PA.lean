/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E35+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e35VH` with `e35VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e35p_partM : triMatF true e35VH e35VP = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e35VH e35VP (e8SrcMatZ.act e35H) (e8SrcMatZ.act e35P)
    (e8SrcMat_act_entryZ e35H) (e8SrcMat_act_entryZ e35P), ← e35PlanP_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e35p_pairChk : pairChk true (e8SrcMatZ.act e35H) e35VH e35VP ((73 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e35p_partP : pairSumQ true e35VH e35VP = ((73 : ℚ) / 4) :=
  pairSumQ_of_chk true e35VH e35VP (e8SrcMatZ.act e35H) (e8SrcMat_act_entryZ e35H) e35p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e35p_octChk : OctadDense.octSumChk 32 4 true e35TH e35TP (255936 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e35p_partO : octSumZ 32 true e35VH e35VP = (255936 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e35VH e35VP e35TH e35TP _ rfl rfl e35p_octChk

/-- The packed octad transform applies. -/
theorem e35p_octOk : octPackOk 32 e35VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e35VH e35TH e35TP _ rfl e35p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
