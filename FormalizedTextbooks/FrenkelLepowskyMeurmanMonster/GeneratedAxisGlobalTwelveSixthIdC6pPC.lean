/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Sixth cell record S6c6+ (gforest:S6c6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s6c6pH_denC : tensorWordDenAll s6c6pH = 65536 := by decide

/-- The tensor denominator of the target word. -/
theorem s6c6pG_den : tensorWordDenAll s6c6pG = 131072 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^22` (one kernel evaluation of the target
tensor). -/
theorem s6c6p_hty : oddLZ 64 true s6c6pGXN s6c6pL = 8153726976 ∧ tdotM 64 s6c6pGXN s6c6pGXN =
    2137450604396544 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s6c6p_htc : tdotM 64 (trialityTensorT 64 (!true) s6c6pHXN) s6c6pGXN = 1068725302198272 := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s6c6p_ht : s6c6pL.sden * (oddLZ 64 true s6c6pGXN s6c6pL : ℚ) / ((tensorWordDenAll s6c6pG :
    ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!true) s6c6pHXN) s6c6pGXN : ℚ) / (2 * ((tensorWordDenAll s6c6pH
        : ℚ) * 32) * ((tensorWordDenAll s6c6pG : ℚ) * 32)) =
      (tdotM 64 s6c6pGXN s6c6pGXN : ℚ) / (((tensorWordDenAll s6c6pG : ℚ) * 32) *
          ((tensorWordDenAll s6c6pG : ℚ) * 32)) := by
  rw [s6c6p_hty.1, s6c6p_hty.2, s6c6p_htc]
  show 1 / 32 * ((8153726976 : ℤ) : ℚ) / ((tensorWordDenAll s6c6pG : ℚ) * 32) +
      ((1068725302198272 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s6c6pH : ℚ) * 32) *
        ((tensorWordDenAll s6c6pG : ℚ) * 32)) =
      ((2137450604396544 : ℤ) : ℚ) / (((tensorWordDenAll s6c6pG : ℚ) * 32) *
        ((tensorWordDenAll s6c6pG : ℚ) * 32))
  rw [s6c6pH_denC, s6c6pG_den]
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
