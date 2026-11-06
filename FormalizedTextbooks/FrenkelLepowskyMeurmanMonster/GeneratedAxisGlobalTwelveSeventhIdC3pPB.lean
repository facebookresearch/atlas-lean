/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (octads) of the identification Seventh cell record S7c3+ (gforest:S7c3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 0..8. -/
theorem s7c3p_hn_n0 :
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT0).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT1).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT2).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT3).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT4).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT5).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT6).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT7).oct +
    octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT8).oct = 33161216 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 0..8. -/
theorem s7c3p_hn_s0 :
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT0).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT1).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT2).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT3).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT4).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT5).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT6).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT7).oct +
    selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT8).oct = 8096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the target fit the packed self sum of field width `48`. -/
theorem s7c3p_wok48 : octPackOk 48 s7c3pW = true := by decide +kernel

/-- The octad part of the pairing. -/
theorem s7c3p_hn_n : octSumZ 40 true s7c3pL s7c3pW = 33161216 := by
  rw [octSumZ_eq_B]
  show octSumB 40 true s7c3pL (ShortData.ofList s7c3pGT).oct = _
  simp only [s7c3pGT, ofList_oct_append, octSumB_append]
  linarith [s7c3p_hn_n0]

/-- The octad self sum of the target. -/
theorem s7c3p_hn_s : selfOctPW 48 s7c3pW = 8096 := by
  rw [selfOctPW_eq_B 48 s7c3pW s7c3p_wok48]
  show selfOctB 48 s7c3pW (ShortData.ofList s7c3pGT).oct = _
  simp only [s7c3pGT, ofList_oct_append, selfOctB_append]
  linarith [s7c3p_hn_s0]

/-- The octad part equals the octad self part of the target. -/
theorem s7c3p_hn : s7c3pL.sden * (octSumZ 40 true s7c3pL s7c3pW : ℚ) / 8 =
    s7c3pW.sden * (selfOctP s7c3pW : ℚ) := by
  rw [s7c3p_hn_n, selfOctP_eq, ← selfOctPW_eq 48, s7c3p_hn_s]
  show 1 / srcSeventhD0 * ((33161216 : ℤ) : ℚ) / 8 = 1 / 16 * ((8096 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
