/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c13+ (gforest:S7c13+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c13pH_den : tensorWordDenAll s7c13pH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c13p_hax : oddWZ 64 true s7c13pHXN s7c13pW = 16698832846848 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c13p_ha_s0 :
    selfOddB s7c13pW (ShortData.ofList s7c13pGT0).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT1).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT2).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT3).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT4).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT5).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT6).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT7).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT8).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT9).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT10).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT11).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT12).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT13).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT14).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT15).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT16).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT17).odd = 615251968 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c13p_ha_s1 :
    selfOddB s7c13pW (ShortData.ofList s7c13pGT18).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT19).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT20).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT21).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT22).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT23).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT24).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT25).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT26).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT27).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT28).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT29).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT30).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT31).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT32).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT33).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT34).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT35).odd = 450625536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c13p_ha_s2 :
    selfOddB s7c13pW (ShortData.ofList s7c13pGT36).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT37).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT38).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT39).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT40).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT41).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT42).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT43).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT44).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT45).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT46).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT47).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT48).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT49).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT50).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT51).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT52).odd +
    selfOddB s7c13pW (ShortData.ofList s7c13pGT53).odd = 972554240 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c13p_wodd : oddPackOk s7c13pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c13p_ha_s : selfOddP s7c13pW = 2038431744 := by
  rw [selfOddP_eq_B s7c13pW s7c13p_wodd]
  show selfOddB s7c13pW (ShortData.ofList s7c13pGT).odd = _
  simp only [s7c13pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c13p_ha_s0, s7c13p_ha_s1, s7c13p_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c13p_ha : (oddWZ 64 true s7c13pHXN s7c13pW : ℚ) / (2 * ((tensorWordDenAll s7c13pH : ℚ) *
    srcSeventhD0)) =
    s7c13pW.sden * (selfOddP s7c13pW : ℚ) := by
  rw [s7c13p_hax, s7c13p_ha_s]
  show ((16698832846848 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c13pH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((2038431744 : ℤ) : ℚ)
  rw [s7c13pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
