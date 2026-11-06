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

/-! # Dense identification E27-: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e27VH` with `e27VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e27m_EH : e27EH = 131072 := by
  unfold e27EH
  rw [show tensorWordDenAll e27H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e27m_EM : e27EM = 262144 := by
  unfold e27EM
  rw [show tensorWordDenAll e27M = 32 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e27m_oddChkA : OddDense.oddChk 64 (256 * 10496) false true e27TM e27XH (234881024 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e27m_partA : oddWZ 64 false e27XH e27VM = (234881024 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e27VM e27TM e27VM_sh e27XH_bnd e27m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e27m_oddChkB : OddDense.oddChk 64 (2048 * 10496) true false e27TH e27XM (469762048 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e27m_partB : oddLZ 64 false e27XM e27VH = (469762048 : ℤ) :=
  TSplit.oddLZ_of_chk2 false e27VH e27TH e27VH_sh e27XM_bnd e27m_oddChkB

set_option maxRecDepth 100000 in
/-- The multiplicative tensor dot product. -/
theorem e27m_tdotM : tdotM 64 (trialityTensorT 64 true e27XH) e27XM = (4672924418048 : ℤ) := by
  decide +kernel

/-- The tensor part. -/
theorem e27m_partC : tdot 64 (trialityTensorT 64 true e27XH) e27XM = (4672924418048 : ℤ) := by
  rw [← tdotM_eq (trialityTensorT_spec true e27XH_bnd (by norm_num)).1 e27XM_bnd (by norm_num)]
  exact e27m_tdotM

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
