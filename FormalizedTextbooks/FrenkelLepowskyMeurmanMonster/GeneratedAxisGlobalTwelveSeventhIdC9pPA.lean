/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c9+
(gforest:S7c9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s7c9p_hok : octPackOk 40 s7c9pL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s7c9p_hm_g0 :
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT0).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT1).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT2).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT3).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT4).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT5).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT6).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT7).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT8).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT9).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT10).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT11).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT12).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT13).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT14).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT15).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT16).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT17).pairs = 90112 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s7c9p_hm_g1 :
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT18).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT19).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT20).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT21).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT22).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT23).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT24).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT25).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT26).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT27).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT28).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT29).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT30).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT31).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT32).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT33).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT34).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT35).pairs = 53248 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s7c9p_hm_g2 :
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT36).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT37).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT38).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT39).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT40).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT41).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT42).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT43).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT44).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT45).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT46).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT47).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT48).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT49).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT50).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT51).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT52).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT53).pairs = 180224 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s7c9p_hp_g0 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT0).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT1).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT2).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT3).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT4).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT5).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT6).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT7).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT8).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT9).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT10).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT11).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT12).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT13).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT14).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT15).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT16).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT17).pairs = (11 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s7c9p_sp_g0 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT0).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT1).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT2).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT3).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT4).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT5).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT6).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT7).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT8).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT9).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT10).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT11).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT12).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT13).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT14).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT15).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT16).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT17).pairs = 1408 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s7c9p_hp_g1 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT18).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT19).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT20).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT21).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT22).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT23).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT24).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT25).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT26).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT27).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT28).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT29).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT30).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT31).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT32).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT33).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT34).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT35).pairs = (31 :
        ℚ) / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s7c9p_sp_g1 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT18).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT19).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT20).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT21).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT22).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT23).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT24).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT25).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT26).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT27).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT28).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT29).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT30).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT31).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT32).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT33).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT34).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT35).pairs = 1984 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s7c9p_hp_g2 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT36).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT37).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT38).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT39).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT40).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT41).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT42).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT43).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT44).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT45).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT46).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT47).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT48).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT49).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT50).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT51).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT52).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT53).pairs = (37 :
        ℚ) / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s7c9p_sp_g2 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT36).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT37).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT38).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT39).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT40).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT41).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT42).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT43).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT44).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT45).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT46).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT47).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT48).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT49).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT50).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT51).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT52).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT53).pairs = 2368 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 54..71. -/
theorem s7c9p_hp_g3 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT54).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT55).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT56).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT57).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT58).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT59).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT60).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT61).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT62).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT63).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT64).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT65).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT66).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT67).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT68).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT69).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT70).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT71).pairs = (9 : ℚ)
        / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 54..71. -/
theorem s7c9p_sp_g3 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT54).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT55).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT56).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT57).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT58).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT59).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT60).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT61).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT62).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT63).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT64).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT65).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT66).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT67).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT68).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT69).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT70).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT71).pairs = 576 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 72..89. -/
theorem s7c9p_hp_g4 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT72).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT73).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT74).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT75).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT76).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT77).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT78).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT79).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT80).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT81).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT82).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT83).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT84).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT85).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT86).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT87).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT88).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT89).pairs = (21 :
        ℚ) / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 72..89. -/
theorem s7c9p_sp_g4 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT72).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT73).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT74).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT75).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT76).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT77).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT78).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT79).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT80).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT81).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT82).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT83).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT84).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT85).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT86).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT87).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT88).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT89).pairs = 1344 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 90..91. -/
theorem s7c9p_hp_g5 :
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT90).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT91).pairs = (1 : ℚ)
        / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 90..91. -/
theorem s7c9p_sp_g5 :
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT90).pairs +
    selfPairsB s7c9pW (ShortData.ofList s7c9pGT91).pairs = 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s7c9p_hm_rest : triMatDiag (srcSeventhMatZ.act s7c9pH) (twelfthSrcMatZ.act s7c9pG) +
    s7c9pL.sden * ((323584 : ℤ) : ℚ) / ((twelfthSrcMatZ.act s7c9pG).den * 4 ^ (twelfthSrcMatZ.act
        s7c9pG).k) = selfMatZI (twelfthSrcMatZ.act s7c9pG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s7c9p_hm : triMatF true s7c9pL s7c9pW = selfMatQ s7c9pW := by
  rw [triMatF_eq_ZI true s7c9pL s7c9pW (srcSeventhMatZ.act s7c9pH) (twelfthSrcMatZ.act s7c9pG)
      (srcSeventhMat_act_entryZ s7c9pH) (twelfthSrcMat_act_entryZ s7c9pG),
    selfMatQ_eq_ZI s7c9pW (twelfthSrcMatZ.act s7c9pG) (twelfthSrcMat_act_entryZ s7c9pG),
        triMatZI_eq_B]
  have hp : triMatPB true (twelfthSrcMatZ.act s7c9pG) s7c9pL.sh.pairs = 323584 := by
    show triMatPB true (twelfthSrcMatZ.act s7c9pG) (ShortData.ofList s7c9pHT).pairs = _
    simp only [s7c9pHT, ofList_pairs_append, triMatPB_append]
    linarith [s7c9p_hm_g0, s7c9p_hm_g1, s7c9p_hm_g2]
  rw [hp]
  exact s7c9p_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s7c9p_hp : pairSumQ true s7c9pL s7c9pW = s7c9pW.sden * (selfPairsZ s7c9pW : ℚ) := by
  rw [pairSumQ_eq_ZI true s7c9pL s7c9pW (srcSeventhMatZ.act s7c9pH) (srcSeventhMat_act_entryZ
      s7c9pH), pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL s7c9pW.sh.pairs = (121 : ℚ) / 2 := by
    show pairSumQB true (srcSeventhMatZ.act s7c9pH) s7c9pL (ShortData.ofList s7c9pGT).pairs = _
    simp only [s7c9pGT, ofList_pairs_append, pairSumQB_append]
    linarith [s7c9p_hp_g0, s7c9p_hp_g1, s7c9p_hp_g2, s7c9p_hp_g3, s7c9p_hp_g4, s7c9p_hp_g5]
  have h2 : selfPairsB s7c9pW s7c9pW.sh.pairs = 7744 := by
    show selfPairsB s7c9pW (ShortData.ofList s7c9pGT).pairs = _
    simp only [s7c9pGT, ofList_pairs_append, selfPairsB_append]
    linarith [s7c9p_sp_g0, s7c9p_sp_g1, s7c9p_sp_g2, s7c9p_sp_g3, s7c9p_sp_g4, s7c9p_sp_g5]
  rw [h1, h2]
  show (121 : ℚ) / 2 = 1 / 128 * ((7744 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
