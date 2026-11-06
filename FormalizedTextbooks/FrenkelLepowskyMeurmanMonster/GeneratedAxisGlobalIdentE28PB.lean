/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28G
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Dense identification E28+: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e28VH` with `e28VG` (`pairTriGMZ`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e28p_EH : e28EH = 131072 := by
  unfold e28EH
  rw [show tensorWordDenAll e28H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e28p_EG : e28EG = 262144 := by
  unfold e28EG
  rw [show tensorWordDenAll e28G = 32 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- The dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e28p_oddChkA : OddDense.oddChk 64 (256 * 10496) true false e28TG e28XH (260046848 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e28p_partA : oddWZ 64 true e28XH e28VG = (260046848 : ℤ) :=
  OddDense.oddWZ_of_chk true e28VH e28VG e28TG e28VG_sh e28VH_ten
    (by rw [e28p_EH]; norm_num) e28XH_bnd e28p_oddChkA

set_option maxRecDepth 100000 in
/-- The dense odd check: odd terms of the source against the tensor of the target. -/
theorem e28p_oddChkB : OddDense.oddChk 64 (2048 * 10496) false true e28TH e28XG (520093696 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e28p_partB : oddLZ 64 true e28XG e28VH = (520093696 : ℤ) :=
  OddDense.oddLZ_of_chk true e28VH e28VG e28TH e28VH_sh e28VG_ten
    (by rw [e28p_EG]; norm_num) (by rw [show e28VH.sden = 1 / 32 from e8SrcVecS_sden]; norm_num)
    e28XG_bnd e28p_oddChkB

set_option maxRecDepth 100000 in
/-- The tensor part. -/
theorem e28p_partC : tdotM 64 (trialityTensorT 64 false e28XH) e28XG = (4260607557632 : ℤ) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
