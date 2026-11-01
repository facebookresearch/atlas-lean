/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC6pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c6+
(gforest:S7c6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s7c6p_hok : octPackOk 40 s7c6pL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s7c6p_hm_g0 :
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT0).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT1).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT2).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT3).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT4).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT5).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT6).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT7).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT8).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT9).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT10).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT11).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT12).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT13).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT14).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT15).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT16).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT17).pairs = 1835008 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s7c6p_hm_g1 :
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT18).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT19).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT20).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT21).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT22).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT23).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT24).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT25).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT26).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT27).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT28).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT29).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT30).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT31).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT32).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT33).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT34).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT35).pairs = 1507328 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s7c6p_hm_g2 :
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT36).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT37).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT38).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT39).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT40).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT41).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT42).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT43).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT44).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT45).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT46).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT47).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT48).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT49).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT50).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT51).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT52).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT53).pairs = 1835008 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s7c6p_hp_g0 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT0).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT1).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT2).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT3).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT4).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT5).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT6).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT7).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT8).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT9).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT10).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT11).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT12).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT13).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT14).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT15).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT16).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT17).pairs = (39 :
        ℚ) / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s7c6p_sp_g0 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT0).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT1).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT2).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT3).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT4).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT5).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT6).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT7).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT8).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT9).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT10).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT11).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT12).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT13).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT14).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT15).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT16).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT17).pairs = 2496 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s7c6p_hp_g1 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT18).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT19).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT20).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT21).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT22).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT23).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT24).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT25).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT26).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT27).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT28).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT29).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT30).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT31).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT32).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT33).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT34).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT35).pairs = (3 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s7c6p_sp_g1 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT18).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT19).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT20).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT21).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT22).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT23).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT24).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT25).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT26).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT27).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT28).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT29).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT30).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT31).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT32).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT33).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT34).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT35).pairs = 384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s7c6p_hp_g2 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT36).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT37).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT38).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT39).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT40).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT41).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT42).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT43).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT44).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT45).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT46).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT47).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT48).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT49).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT50).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT51).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT52).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT53).pairs = (15 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s7c6p_sp_g2 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT36).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT37).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT38).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT39).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT40).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT41).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT42).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT43).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT44).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT45).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT46).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT47).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT48).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT49).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT50).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT51).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT52).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT53).pairs = 1920 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 54..71. -/
theorem s7c6p_hp_g3 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT54).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT55).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT56).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT57).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT58).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT59).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT60).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT61).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT62).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT63).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT64).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT65).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT66).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT67).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT68).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT69).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT70).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT71).pairs = (2 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 54..71. -/
theorem s7c6p_sp_g3 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT54).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT55).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT56).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT57).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT58).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT59).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT60).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT61).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT62).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT63).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT64).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT65).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT66).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT67).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT68).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT69).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT70).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT71).pairs = 256 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 72..89. -/
theorem s7c6p_hp_g4 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT72).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT73).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT74).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT75).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT76).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT77).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT78).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT79).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT80).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT81).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT82).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT83).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT84).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT85).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT86).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT87).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT88).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT89).pairs = (39 :
        ℚ) / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 72..89. -/
theorem s7c6p_sp_g4 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT72).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT73).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT74).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT75).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT76).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT77).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT78).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT79).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT80).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT81).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT82).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT83).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT84).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT85).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT86).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT87).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT88).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT89).pairs = 2496 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 90..91. -/
theorem s7c6p_hp_g5 :
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT90).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT91).pairs = (3 : ℚ)
        / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 90..91. -/
theorem s7c6p_sp_g5 :
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT90).pairs +
    selfPairsB s7c6pW (ShortData.ofList s7c6pGT91).pairs = 192 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s7c6p_hm_rest : triMatDiag (srcSeventhMatZ.act s7c6pH) (twelfthSrcMatZ.act s7c6pG) +
    s7c6pL.sden * ((5177344 : ℤ) : ℚ) / ((twelfthSrcMatZ.act s7c6pG).den * 4 ^ (twelfthSrcMatZ.act
        s7c6pG).k) = selfMatZI (twelfthSrcMatZ.act s7c6pG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s7c6p_hm : triMatF true s7c6pL s7c6pW = selfMatQ s7c6pW := by
  rw [triMatF_eq_ZI true s7c6pL s7c6pW (srcSeventhMatZ.act s7c6pH) (twelfthSrcMatZ.act s7c6pG)
      (srcSeventhMat_act_entryZ s7c6pH) (twelfthSrcMat_act_entryZ s7c6pG),
    selfMatQ_eq_ZI s7c6pW (twelfthSrcMatZ.act s7c6pG) (twelfthSrcMat_act_entryZ s7c6pG),
        triMatZI_eq_B]
  have hp : triMatPB true (twelfthSrcMatZ.act s7c6pG) s7c6pL.sh.pairs = 5177344 := by
    show triMatPB true (twelfthSrcMatZ.act s7c6pG) (ShortData.ofList s7c6pHT).pairs = _
    simp only [s7c6pHT, ofList_pairs_append, triMatPB_append]
    linarith [s7c6p_hm_g0, s7c6p_hm_g1, s7c6p_hm_g2]
  rw [hp]
  exact s7c6p_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s7c6p_hp : pairSumQ true s7c6pL s7c6pW = s7c6pW.sden * (selfPairsZ s7c6pW : ℚ) := by
  rw [pairSumQ_eq_ZI true s7c6pL s7c6pW (srcSeventhMatZ.act s7c6pH) (srcSeventhMat_act_entryZ
      s7c6pH), pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL s7c6pW.sh.pairs = (121 : ℚ) / 2 := by
    show pairSumQB true (srcSeventhMatZ.act s7c6pH) s7c6pL (ShortData.ofList s7c6pGT).pairs = _
    simp only [s7c6pGT, ofList_pairs_append, pairSumQB_append]
    linarith [s7c6p_hp_g0, s7c6p_hp_g1, s7c6p_hp_g2, s7c6p_hp_g3, s7c6p_hp_g4, s7c6p_hp_g5]
  have h2 : selfPairsB s7c6pW s7c6pW.sh.pairs = 7744 := by
    show selfPairsB s7c6pW (ShortData.ofList s7c6pGT).pairs = _
    simp only [s7c6pGT, ofList_pairs_append, selfPairsB_append]
    linarith [s7c6p_sp_g0, s7c6p_sp_g1, s7c6p_sp_g2, s7c6p_sp_g3, s7c6p_sp_g4, s7c6p_sp_g5]
  rw [h1, h2]
  show (121 : ℚ) / 2 = 1 / 128 * ((7744 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
