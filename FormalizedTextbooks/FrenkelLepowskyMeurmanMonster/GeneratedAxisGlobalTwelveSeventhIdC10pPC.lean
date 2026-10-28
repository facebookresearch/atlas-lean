/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c10+ (gforest:S7c10+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c10pH_denC : tensorWordDenAll s7c10pH = 4096 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c10pG_den : tensorWordDenAll s7c10pG = 8192 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^28` (one kernel evaluation of the target
tensor). -/
theorem s7c10p_hty : oddLZ 72 true s7c10pGXN s7c10pL = 34359738368000 ∧ tdotM 72 s7c10pGXN
    s7c10pGXN = 547187354725515264 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c10p_htc : tdotM 72 (trialityTensorT 72 (!true) s7c10pHXN) s7c10pGXN =
    265712378014859264 := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c10p_ht : s7c10pL.sden * (oddLZ 72 true s7c10pGXN s7c10pL : ℚ) / ((tensorWordDenAll
    s7c10pG : ℚ) * srcSeventhD0) +
    (tdotM 72 (trialityTensorT 72 (!true) s7c10pHXN) s7c10pGXN : ℚ) / (2 * ((tensorWordDenAll
        s7c10pH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0)) =
      (tdotM 72 s7c10pGXN s7c10pGXN : ℚ) / (((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0)) := by
  rw [s7c10p_hty.1, s7c10p_hty.2, s7c10p_htc]
  show 1 / srcSeventhD0 * ((34359738368000 : ℤ) : ℚ) / ((tensorWordDenAll s7c10pG : ℚ) *
      srcSeventhD0) +
      ((265712378014859264 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c10pH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0)) =
      ((547187354725515264 : ℤ) : ℚ) / (((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0))
  rw [s7c10pH_denC, s7c10pG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
