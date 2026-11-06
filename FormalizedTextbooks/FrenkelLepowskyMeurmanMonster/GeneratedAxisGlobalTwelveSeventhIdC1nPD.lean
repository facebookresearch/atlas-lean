/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record S7c1-
(gforest:S7c1-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c1nH_den : tensorWordDenAll s7c1nH = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c1n_hax : oddWZ 64 false s7c1nHXN s7c1nW = 1065151889408 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c1n_ha_s0 :
    selfOddB s7c1nW (ShortData.ofList s7c1nGT0).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT1).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT2).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT3).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT4).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT5).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT6).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT7).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT8).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT9).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT10).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT11).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT12).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT13).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT14).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT15).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT16).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT17).odd = 714604544 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c1n_ha_s1 :
    selfOddB s7c1nW (ShortData.ofList s7c1nGT18).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT19).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT20).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT21).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT22).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT23).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT24).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT25).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT26).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT27).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT28).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT29).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT30).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT31).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT32).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT33).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT34).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT35).odd = 393478144 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c1n_ha_s2 :
    selfOddB s7c1nW (ShortData.ofList s7c1nGT36).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT37).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT38).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT39).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT40).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT41).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT42).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT43).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT44).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT45).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT46).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT47).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT48).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT49).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT50).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT51).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT52).odd +
    selfOddB s7c1nW (ShortData.ofList s7c1nGT53).odd = 972292096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c1n_wodd : oddPackOk s7c1nW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c1n_ha_s : selfOddP s7c1nW = 2080374784 := by
  rw [selfOddP_eq_B s7c1nW s7c1n_wodd]
  show selfOddB s7c1nW (ShortData.ofList s7c1nGT).odd = _
  simp only [s7c1nGT, ofList_odd_append, selfOddB_append]
  linarith [s7c1n_ha_s0, s7c1n_ha_s1, s7c1n_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c1n_ha : (oddWZ 64 false s7c1nHXN s7c1nW : ℚ) / (2 * ((tensorWordDenAll s7c1nH : ℚ) *
    srcSeventhD0)) =
    s7c1nW.sden * (selfOddP s7c1nW : ℚ) := by
  rw [s7c1n_hax, s7c1n_ha_s]
  show ((1065151889408 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c1nH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((2080374784 : ℤ) : ℚ)
  rw [s7c1nH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
