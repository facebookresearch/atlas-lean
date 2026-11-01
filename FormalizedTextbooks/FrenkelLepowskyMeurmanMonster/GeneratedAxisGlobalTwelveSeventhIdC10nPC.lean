/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c10- (gforest:S7c10-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c10nH_denC : tensorWordDenAll s7c10nH = 4096 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c10nG_den : tensorWordDenAll s7c10nG = 8192 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^17` (one kernel evaluation of the target
tensor). -/
theorem s7c10n_hty : oddLZ 64 false s7c10nGXN s7c10nL = 134217728000 ∧ tdotM 64 s7c10nGXN
    s7c10nGXN = 8589934592000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c10n_htc : tdotM 64 (trialityTensorT 64 (!false) s7c10nHXN) s7c10nGXN = 1099511627776000
    := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c10n_ht : s7c10nL.sden * (oddLZ 64 false s7c10nGXN s7c10nL : ℚ) / ((tensorWordDenAll
    s7c10nG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!false) s7c10nHXN) s7c10nGXN : ℚ) / (2 * ((tensorWordDenAll
        s7c10nH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c10nG : ℚ) * 32)) =
      (tdotM 64 s7c10nGXN s7c10nGXN : ℚ) / (((tensorWordDenAll s7c10nG : ℚ) * 32) *
          ((tensorWordDenAll s7c10nG : ℚ) * 32)) := by
  rw [s7c10n_hty.1, s7c10n_hty.2, s7c10n_htc]
  show 1 / srcSeventhD0 * ((134217728000 : ℤ) : ℚ) / ((tensorWordDenAll s7c10nG : ℚ) * 32) +
      ((1099511627776000 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c10nH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c10nG : ℚ) * 32)) =
      ((8589934592000 : ℤ) : ℚ) / (((tensorWordDenAll s7c10nG : ℚ) * 32) *
        ((tensorWordDenAll s7c10nG : ℚ) * 32))
  rw [s7c10nH_denC, s7c10nG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
