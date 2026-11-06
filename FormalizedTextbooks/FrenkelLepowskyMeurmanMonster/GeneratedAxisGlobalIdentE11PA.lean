/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E11+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e11VH` with `e11VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e11p_partM : triMatF true e11VH e11VP = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e11VH e11VP (e8SrcMatZ.act e11H) (e8SrcMatZ.act e11P)
    (e8SrcMat_act_entryZ e11H) (e8SrcMat_act_entryZ e11P), ← e11PlanP_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e11p_pairChk : pairChk true (e8SrcMatZ.act e11H) e11VH e11VP ((51 : ℚ) / 4) = true := by
  decide +kernel

/-- The pair part. -/
theorem e11p_partP : pairSumQ true e11VH e11VP = ((51 : ℚ) / 4) :=
  pairSumQ_of_chk true e11VH e11VP (e8SrcMatZ.act e11H) (e8SrcMat_act_entryZ e11H) e11p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e11p_octChk : OctadDense.octSumChk 32 4 true e11TH e11TP (257344 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e11p_partO : octSumZ 32 true e11VH e11VP = (257344 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e11VH e11VP e11TH e11TP _ rfl rfl e11p_octChk

/-- The packed octad transform applies. -/
theorem e11p_octOk : octPackOk 32 e11VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e11VH e11TH e11TP _ rfl e11p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
