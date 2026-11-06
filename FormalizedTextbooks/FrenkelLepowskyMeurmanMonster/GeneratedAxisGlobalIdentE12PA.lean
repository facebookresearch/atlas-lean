/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E12+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e12VH` with `e12VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e12p_partM : triMatF true e12VH e12VP = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e12VH e12VP (e8SrcMatZ.act e12H) (e8SrcMatZ.act e12P)
    (e8SrcMat_act_entryZ e12H) (e8SrcMat_act_entryZ e12P), ← e12PlanP_word, ← MatZ.actT_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (packed lookups). -/
theorem e12p_pairChk : pairChk true (e8SrcMatZ.act e12H) e12VH e12VP ((105 : ℚ) / 8) = true := by
  decide +kernel

/-- The pair part. -/
theorem e12p_partP : pairSumQ true e12VH e12VP = ((105 : ℚ) / 8) :=
  pairSumQ_of_chk true e12VH e12VP (e8SrcMatZ.act e12H) (e8SrcMat_act_entryZ e12H) e12p_pairChk

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e12p_octChk : OctadDense.octSumChk 32 4 true e12TH e12TP (256224 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e12p_partO : octSumZ 32 true e12VH e12VP = (256224 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e12VH e12VP e12TH e12TP _ rfl rfl e12p_octChk

/-- The packed octad transform applies. -/
theorem e12p_octOk : octPackOk 32 e12VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e12VH e12TH e12TP _ rfl e12p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
