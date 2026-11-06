/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c20- (gforest:S7c20-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c20nH_den : tensorWordDenAll s7c20nH = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing, and the fields of the source tensor are below `2^29`
(one kernel evaluation of the source tensor). -/
theorem s7c20n_hax : oddWZ 80 false s7c20nHX s7c20nW = 962072674304 ∧ colsLtB 80 29 s7c20nHX =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c20n_ha_s0 :
    selfOddB s7c20nW (ShortData.ofList s7c20nGT0).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT1).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT2).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT3).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT4).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT5).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT6).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT7).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT8).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT9).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT10).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT11).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT12).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT13).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT14).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT15).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT16).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT17).odd = 563609600 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c20n_ha_s1 :
    selfOddB s7c20nW (ShortData.ofList s7c20nGT18).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT19).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT20).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT21).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT22).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT23).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT24).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT25).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT26).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT27).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT28).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT29).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT30).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT31).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT32).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT33).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT34).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT35).odd = 343146496 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c20n_ha_s2 :
    selfOddB s7c20nW (ShortData.ofList s7c20nGT36).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT37).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT38).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT39).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT40).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT41).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT42).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT43).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT44).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT45).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT46).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT47).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT48).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT49).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT50).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT51).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT52).odd +
    selfOddB s7c20nW (ShortData.ofList s7c20nGT53).odd = 972292096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c20n_wodd : oddPackOk s7c20nW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c20n_ha_s : selfOddP s7c20nW = 1879048192 := by
  rw [selfOddP_eq_B s7c20nW s7c20n_wodd]
  show selfOddB s7c20nW (ShortData.ofList s7c20nGT).odd = _
  simp only [s7c20nGT, ofList_odd_append, selfOddB_append]
  linarith [s7c20n_ha_s0, s7c20n_ha_s1, s7c20n_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c20n_ha : (oddWZ 80 false s7c20nHX s7c20nW : ℚ) / (2 * ((tensorWordDenAll s7c20nH : ℚ) *
    srcSeventhD0)) =
    s7c20nW.sden * (selfOddP s7c20nW : ℚ) := by
  rw [s7c20n_hax.1, s7c20n_ha_s]
  show ((962072674304 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c20nH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((1879048192 : ℤ) : ℚ)
  rw [s7c20nH_den]
  norm_num [srcSeventhD0_eq]

/-- The fields of the source tensor are below `2^29`. -/
theorem s7c20n_xlt : colsLtB 80 29 s7c20nHX = true := s7c20n_hax.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
