/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c19+ (gforest:S7c19+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c19pH_den : tensorWordDenAll s7c19pH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c19p_hax : oddWZ 72 true s7c19pHXN s7c19pW = 16698832846848 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c19p_ha_s0 :
    selfOddB s7c19pW (ShortData.ofList s7c19pGT0).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT1).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT2).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT3).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT4).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT5).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT6).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT7).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT8).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT9).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT10).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT11).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT12).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT13).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT14).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT15).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT16).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT17).odd = 657195008 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c19p_ha_s1 :
    selfOddB s7c19pW (ShortData.ofList s7c19pGT18).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT19).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT20).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT21).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT22).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT23).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT24).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT25).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT26).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT27).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT28).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT29).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT30).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT31).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT32).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT33).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT34).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT35).odd = 408944640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c19p_ha_s2 :
    selfOddB s7c19pW (ShortData.ofList s7c19pGT36).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT37).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT38).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT39).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT40).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT41).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT42).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT43).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT44).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT45).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT46).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT47).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT48).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT49).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT50).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT51).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT52).odd +
    selfOddB s7c19pW (ShortData.ofList s7c19pGT53).odd = 972292096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c19p_wodd : oddPackOk s7c19pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c19p_ha_s : selfOddP s7c19pW = 2038431744 := by
  rw [selfOddP_eq_B s7c19pW s7c19p_wodd]
  show selfOddB s7c19pW (ShortData.ofList s7c19pGT).odd = _
  simp only [s7c19pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c19p_ha_s0, s7c19p_ha_s1, s7c19p_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c19p_ha : (oddWZ 72 true s7c19pHXN s7c19pW : ℚ) / (2 * ((tensorWordDenAll s7c19pH : ℚ) *
    srcSeventhD0)) =
    s7c19pW.sden * (selfOddP s7c19pW : ℚ) := by
  rw [s7c19p_hax, s7c19p_ha_s]
  show ((16698832846848 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c19pH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((2038431744 : ℤ) : ℚ)
  rw [s7c19pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
