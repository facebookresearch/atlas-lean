/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual two-core conjugation transport with complete checked binary action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportLineProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint089
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 159. -/
def monsterCo1GeometryVectorPoint159Transport : Co1 :=
  monsterCo1GeometryVectorPoint89Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint89Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 159. -/
def monsterCo1GeometryVectorPoint159Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 7290999, 14423381, 6115247, 14839615, 15568324, 13805880, 6131327,
      14519565, 3364306, 9679632, 14507711, 16344378, 6945250, 14237625, 16544320, 11820062,
      14615858, 7198740, 15857735, 723164, 6740523, 12526802]

/-- First complete finite matrix product in literal actual transport 159. -/
def monsterCo1GeometryVectorPoint159AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
      12639278, 1106944, 12919938, 2000070, 1426060, 3529091, 2481027, 12838964, 13110277,
      12773400, 13372425, 78860, 8704140, 1440803, 8445952]

/-- Second complete finite matrix product in literal actual transport 159. -/
def monsterCo1GeometryVectorPoint159AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4228111, 4211727, 2752576, 1377420, 2752528, 1377324, 2752848, 1377964, 8437760,
      4194572, 53534, 57437, 11192667, 11192663, 1312239, 2621520, 1115582, 2228304, 9438301,
      2097152, 2804048, 1036]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 159 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint159Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint159Transport v =
      monsterCo1GeometryVectorPoint159Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint89Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368] := by rfl
  have hxi : monsterCo1GeometryVectorPoint89InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 13626704, 8191582, 7544415, 8389918, 81, 8390287, 161, 4211719, 49164, 12517616,
    8381197, 1377452, 4128769, 12519231, 12519374, 712705, 10621198, 385025, 9761295, 49152,
    4211725, 4188400, 4130044] := by rfl
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint159AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 1106944, 12919938, 2000070, 1426060, 3529091, 2481027, 12838964, 13110277,
    12773400, 13372425, 78860, 8704140, 1440803, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint159AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4228111, 4211727, 2752576, 1377420, 2752528, 1377324, 2752848, 1377964, 8437760,
    4194572, 53534, 57437, 11192667, 11192663, 1312239, 2621520, 1115582, 2228304, 9438301,
    2097152, 2804048, 1036] := by rfl
  have hc : monsterCo1GeometryVectorPoint159Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 7290999, 14423381, 6115247, 14839615, 15568324, 13805880, 6131327,
    14519565, 3364306, 9679632, 14507711, 16344378, 6945250, 14237625, 16544320, 11820062,
    14615858, 7198740, 15857735, 723164, 6740523, 12526802] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint89Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint159AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 8414416, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 1106944, 12919938, 2000070, 1426060, 3529091, 2481027, 12838964, 13110277,
    12773400, 13372425, 78860, 8704140, 1440803, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint159AfterSignMatrix *
    monsterCo1GeometryVectorPoint89InverseMatrix =
    monsterCo1GeometryVectorPoint159AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8414416, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 1106944, 12919938, 2000070, 1426060, 3529091, 2481027, 12838964, 13110277,
    12773400, 13372425, 78860, 8704140, 1440803, 8445952]
    ![1008, 13626704, 8191582, 7544415, 8389918, 81, 8390287, 161, 4211719, 49164, 12517616,
    8381197, 1377452, 4128769, 12519231, 12519374, 712705, 10621198, 385025, 9761295, 49152,
    4211725, 4188400, 4130044]
    ![1, 2, 4228111, 4211727, 2752576, 1377420, 2752528, 1377324, 2752848, 1377964, 8437760,
    4194572, 53534, 57437, 11192667, 11192663, 1312239, 2621520, 1115582, 2228304, 9438301,
    2097152, 2804048, 1036] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint159AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint159Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 4228111, 4211727, 2752576, 1377420, 2752528, 1377324, 2752848, 1377964, 8437760,
    4194572, 53534, 57437, 11192667, 11192663, 1312239, 2621520, 1115582, 2228304, 9438301,
    2097152, 2804048, 1036]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![11585126, 12575234, 7290999, 14423381, 6115247, 14839615, 15568324, 13805880, 6131327,
    14519565, 3364306, 9679632, 14507711, 16344378, 6945250, 14237625, 16544320, 11820062,
    14615858, 7198740, 15857735, 723164, 6740523, 12526802] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint89Transport monsterCo1GeometryVectorPoint154Transport 1
    monsterCo1GeometryVectorPoint89Matrix monsterCo1GeometryVectorPoint89InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint159AfterSignMatrix
    monsterCo1GeometryVectorPoint159AfterInverseMatrix monsterCo1GeometryVectorPoint159Matrix
    monsterCo1GeometryVectorPoint89Transport_binary
    monsterCo1GeometryVectorPoint89Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 159 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint159 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint159Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint159_binary :
    monsterCo1GeometryVectorPoint159.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint159Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint159Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
