/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E25+: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e25VH` with `e25VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e25p_EH : e25EH = 131072 := by
  unfold e25EH
  rw [show tensorWordDenAll e25H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e25p_EP : e25EP = 262144 := by
  unfold e25EP
  rw [show tensorWordDenAll e25P = 32 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e25p_oddChkA : OddDense.oddChk 64 (256 * 10496) true false e25TP e25XH (268435456 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e25p_partA : oddWZ 64 true e25XH e25VP = (268435456 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e25VP e25TP e25VP_sh e25XH_bnd e25p_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e25p_oddChkB : OddDense.oddChk 64 (2048 * 10496) false true e25TH e25XP (536870912 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e25p_partB : oddLZ 64 true e25XP e25VH = (536870912 : ℤ) :=
  TSplit.oddLZ_of_chk2 true e25VH e25TH e25VH_sh e25XP_bnd e25p_oddChkB

set_option maxRecDepth 100000 in
/-- The multiplicative tensor dot product. -/
theorem e25p_tdotM : tdotM 64 (trialityTensorT 64 false e25XH) e25XP = (4123168604160 : ℤ) := by
  decide +kernel

/-- The tensor part. -/
theorem e25p_partC : tdot 64 (trialityTensorT 64 false e25XH) e25XP = (4123168604160 : ℤ) := by
  rw [← tdotM_eq (trialityTensorT_spec false e25XH_bnd (by norm_num)).1 e25XP_bnd (by norm_num)]
  exact e25p_tdotM

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
