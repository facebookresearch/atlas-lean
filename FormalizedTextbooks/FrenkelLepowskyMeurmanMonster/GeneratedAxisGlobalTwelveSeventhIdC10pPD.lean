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

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c10+ (gforest:S7c10+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c10pH_den : tensorWordDenAll s7c10pH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c10p_hax : oddWZ 72 true s7c10pHXN s7c10pW = 17179869184000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c10p_ha_s0 :
    selfOddB s7c10pW (ShortData.ofList s7c10pGT0).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT1).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT2).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT3).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT4).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT5).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT6).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT7).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT8).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT9).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT10).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT11).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT12).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT13).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT14).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT15).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT16).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT17).odd = 709623808 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c10p_ha_s1 :
    selfOddB s7c10pW (ShortData.ofList s7c10pGT18).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT19).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT20).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT21).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT22).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT23).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT24).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT25).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT26).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT27).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT28).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT29).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT30).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT31).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT32).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT33).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT34).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT35).odd = 448790528 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c10p_ha_s2 :
    selfOddB s7c10pW (ShortData.ofList s7c10pGT36).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT37).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT38).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT39).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT40).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT41).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT42).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT43).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT44).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT45).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT46).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT47).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT48).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT49).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT50).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT51).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT52).odd +
    selfOddB s7c10pW (ShortData.ofList s7c10pGT53).odd = 938737664 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c10p_wodd : oddPackOk s7c10pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c10p_ha_s : selfOddP s7c10pW = 2097152000 := by
  rw [selfOddP_eq_B s7c10pW s7c10p_wodd]
  show selfOddB s7c10pW (ShortData.ofList s7c10pGT).odd = _
  simp only [s7c10pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c10p_ha_s0, s7c10p_ha_s1, s7c10p_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c10p_ha : (oddWZ 72 true s7c10pHXN s7c10pW : ℚ) / (2 * ((tensorWordDenAll s7c10pH : ℚ) *
    srcSeventhD0)) =
    s7c10pW.sden * (selfOddP s7c10pW : ℚ) := by
  rw [s7c10p_hax, s7c10p_ha_s]
  show ((17179869184000 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c10pH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((2097152000 : ℤ) : ℚ)
  rw [s7c10pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
