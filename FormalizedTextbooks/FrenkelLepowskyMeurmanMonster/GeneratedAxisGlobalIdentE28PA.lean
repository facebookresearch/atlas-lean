/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28G

/-! # Dense identification E28+: matrix, pair and octad parts of the pairing

Pairing of the triality image (`fwd = true`) of `e28VH` with `e28VG` (`pairTriGMZ`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part. -/
theorem e28p_partM : triMatF true e28VH e28VG = ((47 : ℚ) / 16) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part. -/
theorem e28p_partP : pairSumQ true e28VH e28VG = (14 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The dense octad check (packed chunks, field width `32`, field bound `2^4`). -/
theorem e28p_octChk : OctadDense.octSumChk 32 4 true e28TH e28TG (259072 : ℤ) = true := by
  decide +kernel

/-- The octad part. -/
theorem e28p_partO : octSumZ 32 true e28VH e28VG = (259072 : ℤ) :=
  OctadDense.octSumZ_of_chk 32 4 true e28VH e28VG e28TH e28TG _ rfl rfl e28p_octChk

/-- The packed octad transform applies. -/
theorem e28p_octOk : octPackOk 32 e28VH = true :=
  OctadDense.octPackOk_of_chk 32 4 true e28VH e28TH e28TG _ rfl e28p_octChk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
