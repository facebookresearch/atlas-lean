/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth

/-! # Parts (octad check, matrix, pairs) of the identification Sixth cell record S6c1-
(gforest:S6c1-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s6c1n_hok : octPackOk 40 s6c1nL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s6c1n_hm_g0 :
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT0).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT1).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT2).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT3).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT4).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT5).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT6).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT7).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT8).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT9).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT10).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT11).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT12).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT13).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT14).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT15).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT16).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT17).pairs = 3328 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s6c1n_hm_g1 :
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT18).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT19).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT20).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT21).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT22).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT23).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT24).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT25).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT26).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT27).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT28).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT29).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT30).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT31).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT32).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT33).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT34).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT35).pairs = 512 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s6c1n_hm_g2 :
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT36).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT37).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT38).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT39).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT40).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT41).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT42).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT43).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT44).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT45).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT46).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT47).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT48).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT49).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT50).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT51).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT52).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT53).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 54..59. -/
theorem s6c1n_hm_g3 :
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT54).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT55).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT56).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT57).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT58).pairs +
    triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT59).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s6c1n_hp_g0 :
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT0).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT1).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT2).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT3).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT4).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT5).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT6).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT7).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT8).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT9).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT10).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT11).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT12).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT13).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT14).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT15).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT16).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT17).pairs = (10432 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s6c1n_sp_g0 :
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT0).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT1).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT2).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT3).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT4).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT5).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT6).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT7).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT8).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT9).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT10).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT11).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT12).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT13).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT14).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT15).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT16).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT17).pairs = 85458944 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s6c1n_hp_g1 :
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT18).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT19).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT20).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT21).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT22).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT23).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT24).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT25).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT26).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT27).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT28).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT29).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT30).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT31).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT32).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT33).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT34).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT35).pairs = (0 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s6c1n_sp_g1 :
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT18).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT19).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT20).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT21).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT22).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT23).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT24).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT25).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT26).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT27).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT28).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT29).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT30).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT31).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT32).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT33).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT34).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT35).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s6c1n_hp_g2 :
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT36).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT37).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT38).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT39).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT40).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT41).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT42).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT43).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT44).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT45).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT46).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT47).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT48).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT49).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT50).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT51).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT52).pairs +
    pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT53).pairs = (0 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s6c1n_sp_g2 :
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT36).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT37).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT38).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT39).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT40).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT41).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT42).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT43).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT44).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT45).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT46).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT47).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT48).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT49).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT50).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT51).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT52).pairs +
    selfPairsB s6c1nW (ShortData.ofList s6c1nGT53).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s6c1n_hm_rest : triMatDiag (sixthSrcMatZ.act s6c1nH) (srcSeventhMatZ.act s6c1nG) +
    s6c1nL.sden * ((3840 : ℤ) : ℚ) / ((srcSeventhMatZ.act s6c1nG).den * 4 ^ (srcSeventhMatZ.act
        s6c1nG).k) = selfMatZI (srcSeventhMatZ.act s6c1nG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s6c1n_hm : triMatF false s6c1nL s6c1nW = selfMatQ s6c1nW := by
  rw [triMatF_eq_ZI false s6c1nL s6c1nW (sixthSrcMatZ.act s6c1nH) (srcSeventhMatZ.act s6c1nG)
      (sixthSrcMat_act_entryZ s6c1nH) (srcSeventhMat_act_entryZ s6c1nG),
    selfMatQ_eq_ZI s6c1nW (srcSeventhMatZ.act s6c1nG) (srcSeventhMat_act_entryZ s6c1nG),
        triMatZI_eq_B]
  have hp : triMatPB false (srcSeventhMatZ.act s6c1nG) s6c1nL.sh.pairs = 3840 := by
    show triMatPB false (srcSeventhMatZ.act s6c1nG) (ShortData.ofList s6c1nHT).pairs = _
    simp only [s6c1nHT, ofList_pairs_append, triMatPB_append]
    linarith [s6c1n_hm_g0, s6c1n_hm_g1, s6c1n_hm_g2, s6c1n_hm_g3]
  rw [hp]
  exact s6c1n_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s6c1n_hp : pairSumQ false s6c1nL s6c1nW = s6c1nW.sden * (selfPairsZ s6c1nW : ℚ) := by
  rw [pairSumQ_eq_ZI false s6c1nL s6c1nW (sixthSrcMatZ.act s6c1nH) (sixthSrcMat_act_entryZ
      s6c1nH), pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL s6c1nW.sh.pairs = (10432 : ℚ) := by
    show pairSumQB false (sixthSrcMatZ.act s6c1nH) s6c1nL (ShortData.ofList s6c1nGT).pairs = _
    simp only [s6c1nGT, ofList_pairs_append, pairSumQB_append]
    linarith [s6c1n_hp_g0, s6c1n_hp_g1, s6c1n_hp_g2]
  have h2 : selfPairsB s6c1nW s6c1nW.sh.pairs = 85458944 := by
    show selfPairsB s6c1nW (ShortData.ofList s6c1nGT).pairs = _
    simp only [s6c1nGT, ofList_pairs_append, selfPairsB_append]
    linarith [s6c1n_sp_g0, s6c1n_sp_g1, s6c1n_sp_g2]
  rw [h1, h2]
  show (10432 : ℚ) = 1 / srcSeventhD0 * ((85458944 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
