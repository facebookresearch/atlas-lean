/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ

/-! # Dense identification E6+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e6VH` with `e6VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part (integer form). -/
theorem e6p_partM : triMatF true e6VH e6VP = ((47 : ℚ) / 16) := by
  rw [triMatF_eq_ZI true e6VH e6VP (e8SrcMatZ.act e6H) (e8SrcMatZ.act e6P)
    (e8SrcMat_act_entryZ e6H) (e8SrcMat_act_entryZ e6P)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part (integer form). -/
theorem e6p_partP : pairSumQ true e6VH e6VP = (15 : ℚ) := by
  rw [pairSumQ_eq_ZI true e6VH e6VP (e8SrcMatZ.act e6H) (e8SrcMat_act_entryZ e6H)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e6p_octChk : OctadDense.octSumChk 32 4 true e6TH e6TP (258816 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e6p_partO : octSumZ 32 true e6VH e6VP = (258816 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e6VH e6VP e6TH e6TP _ rfl rfl e6p_octChk

/-- The packed octad transform applies. -/
theorem e6p_octOk : octPackOk 32 e6VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e6VH e6TH e6TP _ rfl e6p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
