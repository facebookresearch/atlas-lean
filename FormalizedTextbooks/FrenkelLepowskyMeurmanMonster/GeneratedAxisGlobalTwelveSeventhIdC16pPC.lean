/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c16+ (gforest:S7c16+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c16pH_denC : tensorWordDenAll s7c16pH = 65536 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c16pG_den : tensorWordDenAll s7c16pG = 512 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^13` (one kernel evaluation of the target
tensor). -/
theorem s7c16p_hty : oddLZ 64 true s7c16pGXN s7c16pL = 8623489024 ∧ tdotM 64 s7c16pGXN s7c16pGXN =
    33554432000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c16p_htc : tdotM 64 (trialityTensorT 64 (!true) s7c16pHXN) s7c16pGXN = 1068725302198272
    := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c16p_ht : s7c16pL.sden * (oddLZ 64 true s7c16pGXN s7c16pL : ℚ) / ((tensorWordDenAll
    s7c16pG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!true) s7c16pHXN) s7c16pGXN : ℚ) / (2 * ((tensorWordDenAll
        s7c16pH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c16pG : ℚ) * 32)) =
      (tdotM 64 s7c16pGXN s7c16pGXN : ℚ) / (((tensorWordDenAll s7c16pG : ℚ) * 32) *
          ((tensorWordDenAll s7c16pG : ℚ) * 32)) := by
  rw [s7c16p_hty.1, s7c16p_hty.2, s7c16p_htc]
  show 1 / srcSeventhD0 * ((8623489024 : ℤ) : ℚ) / ((tensorWordDenAll s7c16pG : ℚ) * 32) +
      ((1068725302198272 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c16pH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c16pG : ℚ) * 32)) =
      ((33554432000 : ℤ) : ℚ) / (((tensorWordDenAll s7c16pG : ℚ) * 32) *
        ((tensorWordDenAll s7c16pG : ℚ) * 32))
  rw [s7c16pH_denC, s7c16pG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
