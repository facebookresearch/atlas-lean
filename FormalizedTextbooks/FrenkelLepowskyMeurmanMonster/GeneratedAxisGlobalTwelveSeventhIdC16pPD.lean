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

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c16+ (gforest:S7c16+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c16pH_den : tensorWordDenAll s7c16pH = 65536 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c16p_hax : oddWZ 64 true s7c16pHXN s7c16pW = 4174708211712 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c16p_ha_s0 :
    selfOddB s7c16pW (ShortData.ofList s7c16pGT0).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT1).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT2).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT3).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT4).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT5).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT6).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT7).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT8).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT9).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT10).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT11).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT12).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT13).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT14).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT15).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT16).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT17).odd = 132608 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c16p_ha_s1 :
    selfOddB s7c16pW (ShortData.ofList s7c16pGT18).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT19).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT20).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT21).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT22).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT23).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT24).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT25).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT26).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT27).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT28).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT29).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT30).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT31).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT32).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT33).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT34).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT35).odd = 122528 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c16p_ha_s2 :
    selfOddB s7c16pW (ShortData.ofList s7c16pGT36).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT37).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT38).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT39).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT40).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT41).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT42).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT43).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT44).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT45).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT46).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT47).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT48).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT49).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT50).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT51).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT52).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT53).odd = 138816 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 54..65. -/
theorem s7c16p_ha_s3 :
    selfOddB s7c16pW (ShortData.ofList s7c16pGT54).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT55).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT56).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT57).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT58).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT59).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT60).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT61).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT62).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT63).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT64).odd +
    selfOddB s7c16pW (ShortData.ofList s7c16pGT65).odd = 103712 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c16p_wodd : oddPackOk s7c16pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c16p_ha_s : selfOddP s7c16pW = 497664 := by
  rw [selfOddP_eq_B s7c16pW s7c16p_wodd]
  show selfOddB s7c16pW (ShortData.ofList s7c16pGT).odd = _
  simp only [s7c16pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c16p_ha_s0, s7c16p_ha_s1, s7c16p_ha_s2, s7c16p_ha_s3]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c16p_ha : (oddWZ 64 true s7c16pHXN s7c16pW : ℚ) / (2 * ((tensorWordDenAll s7c16pH : ℚ) *
    srcSeventhD0)) =
    s7c16pW.sden * (selfOddP s7c16pW : ℚ) := by
  rw [s7c16p_hax, s7c16p_ha_s]
  show ((4174708211712 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c16pH : ℚ) * srcSeventhD0)) =
    1 / 128 * ((497664 : ℤ) : ℚ)
  rw [s7c16pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
