/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c3+ (gforest:S7c3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c3pH_denC : tensorWordDenAll s7c3pH = 256 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c3pG_den : tensorWordDenAll s7c3pG = 131072 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^16` (one kernel evaluation of the target
tensor). -/
theorem s7c3p_hty : oddLZ 64 true s7c3pGXN s7c3pL = 68719476736 ∧ tdotM 64 s7c3pGXN s7c3pGXN =
    2199023255552 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c3p_htc : tdotM 64 (trialityTensorT 64 (!true) s7c3pHXN) s7c3pGXN = 35184372088832 := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c3p_ht : s7c3pL.sden * (oddLZ 64 true s7c3pGXN s7c3pL : ℚ) / ((tensorWordDenAll s7c3pG :
    ℚ) * 1) +
    (tdotM 64 (trialityTensorT 64 (!true) s7c3pHXN) s7c3pGXN : ℚ) / (2 * ((tensorWordDenAll s7c3pH
        : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c3pG : ℚ) * 1)) =
      (tdotM 64 s7c3pGXN s7c3pGXN : ℚ) / (((tensorWordDenAll s7c3pG : ℚ) * 1) * ((tensorWordDenAll
          s7c3pG : ℚ) * 1)) := by
  rw [s7c3p_hty.1, s7c3p_hty.2, s7c3p_htc]
  show 1 / srcSeventhD0 * ((68719476736 : ℤ) : ℚ) / ((tensorWordDenAll s7c3pG : ℚ) * 1) +
      ((35184372088832 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c3pH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c3pG : ℚ) * 1)) =
      ((2199023255552 : ℤ) : ℚ) / (((tensorWordDenAll s7c3pG : ℚ) * 1) *
        ((tensorWordDenAll s7c3pG : ℚ) * 1))
  rw [s7c3pH_denC, s7c3pG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
