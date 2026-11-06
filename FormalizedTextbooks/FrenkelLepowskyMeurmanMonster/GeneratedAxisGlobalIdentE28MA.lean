/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28Gm

/-! # Dense identification E28-: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = false`) of `e28VH` with `e28VGm` (`pairTriGMZ`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part. -/
theorem e28m_partM : triMatF false e28VH e28VGm = ((47 : ℚ) / 16) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part. -/
theorem e28m_partP : pairSumQ false e28VH e28VGm = (14 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e28m_octChk : OctadDense.octSumChk 32 4 false e28TH e28TGm (259072 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e28m_partO : octSumZ 32 false e28VH e28VGm = (259072 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 false e28VH e28VGm e28TH e28TGm _ rfl rfl e28m_octChk

/-- The packed octad transform applies. -/
theorem e28m_octOk : octPackOk 32 e28VH = true :=
  OctadDense.octPackOk_of_chk 32 4 false e28VH e28TH e28TGm _ rfl e28m_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
