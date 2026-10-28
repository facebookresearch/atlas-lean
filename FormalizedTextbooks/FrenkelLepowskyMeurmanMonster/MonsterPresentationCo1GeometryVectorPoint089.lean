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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 89. -/
def monsterCo1GeometryVectorPoint89Transport : Co1 :=
  monsterCo1GeometryVectorPoint32Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint32Transport⁻¹ * monsterCo1GeometryVectorPoint40Transport

/-- Complete displayed binary matrix of actual transport 89. -/
def monsterCo1GeometryVectorPoint89Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
      12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
      4389896, 4987913, 8466476, 8704140, 1436173, 58368]

/-- First complete finite matrix product in literal actual transport 89. -/
def monsterCo1GeometryVectorPoint89AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8422352, 34256, 8433728, 21552, 8417472, 37904, 8441984, 13344, 58880,
      10820643, 976406, 9822252, 6683437, 16063277, 12811348, 4775157, 12770536, 5029017,
      12683410, 12889315, 12966797, 8389632]

/-- Second complete finite matrix product in literal actual transport 89. -/
def monsterCo1GeometryVectorPoint89AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 8389632, 7006220,
      5406, 8285, 8405259, 8421639, 66531, 131408, 263090, 524624, 1050365, 2097488, 4194561,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 89 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint89Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint89Transport v =
      monsterCo1GeometryVectorPoint89Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint32Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint32InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129536, 6619799, 5641335, 5896167, 8389918, 81, 8390287, 161, 10, 8388620, 2044,
    8366321, 8390316, 769, 8389695, 8389838, 713184, 2234224, 385648, 1374176, 8438784,
    4211719, 8408054, 8390652] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint40Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint89AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8422352, 34256, 8433728, 21552, 8417472, 37904, 8441984, 13344, 58880,
    10820643, 976406, 9822252, 6683437, 16063277, 12811348, 4775157, 12770536, 5029017,
    12683410, 12889315, 12966797, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint89AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 8389632, 7006220,
    5406, 8285, 8405259, 8421639, 66531, 131408, 263090, 524624, 1050365, 2097488, 4194561,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint89Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint32Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint89AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 8422352, 34256, 8433728, 21552, 8417472, 37904, 8441984, 13344, 58880,
    10820643, 976406, 9822252, 6683437, 16063277, 12811348, 4775157, 12770536, 5029017,
    12683410, 12889315, 12966797, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint89AfterSignMatrix *
    monsterCo1GeometryVectorPoint32InverseMatrix =
    monsterCo1GeometryVectorPoint89AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 8422352, 34256, 8433728, 21552, 8417472, 37904, 8441984, 13344, 58880,
    10820643, 976406, 9822252, 6683437, 16063277, 12811348, 4775157, 12770536, 5029017,
    12683410, 12889315, 12966797, 8389632]
    ![4129536, 6619799, 5641335, 5896167, 8389918, 81, 8390287, 161, 10, 8388620, 2044,
    8366321, 8390316, 769, 8389695, 8389838, 713184, 2234224, 385648, 1374176, 8438784,
    4211719, 8408054, 8390652]
    ![1, 8388610, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 8389632, 7006220,
    5406, 8285, 8405259, 8421639, 66531, 131408, 263090, 524624, 1050365, 2097488, 4194561,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint89AfterInverseMatrix *
    monsterCo1GeometryVectorPoint40Matrix = monsterCo1GeometryVectorPoint89Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 8389632, 7006220,
    5406, 8285, 8405259, 8421639, 66531, 131408, 263090, 524624, 1050365, 2097488, 4194561,
    8388608]
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368]
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint32Transport monsterCo1GeometryVectorPoint40Transport 1
    monsterCo1GeometryVectorPoint32Matrix monsterCo1GeometryVectorPoint32InverseMatrix
    monsterCo1GeometryVectorPoint40Matrix
    monsterCo1GeometryVectorPoint89AfterSignMatrix
    monsterCo1GeometryVectorPoint89AfterInverseMatrix monsterCo1GeometryVectorPoint89Matrix
    monsterCo1GeometryVectorPoint32Transport_binary
    monsterCo1GeometryVectorPoint32Transport_inverse_binary
    monsterCo1GeometryVectorPoint40Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 89. -/
def monsterCo1GeometryVectorPoint89InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1008, 13626704, 8191582, 7544415, 8389918, 81, 8390287, 161, 4211719, 49164, 12517616,
      8381197, 1377452, 4128769, 12519231, 12519374, 712705, 10621198, 385025, 9761295, 49152,
      4211725, 4188400, 4130044]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint89Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint89Transport⁻¹ v =
      monsterCo1GeometryVectorPoint89InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint89Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
        12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
        4389896, 4987913, 8466476, 8704140, 1436173, 58368] := by rfl
  have hmi : monsterCo1GeometryVectorPoint89InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![1008, 13626704, 8191582, 7544415, 8389918, 81, 8390287, 161, 4211719, 49164, 12517616,
        8381197, 1377452, 4128769, 12519231, 12519374, 712705, 10621198, 385025, 9761295,
        49152, 4211725, 4188400, 4130044] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint89Matrix *
    monsterCo1GeometryVectorPoint89InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
        12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
        4389896, 4987913, 8466476, 8704140, 1436173, 58368]
      ![1008, 13626704, 8191582, 7544415, 8389918, 81, 8390287, 161, 4211719, 49164, 12517616,
        8381197, 1377452, 4128769, 12519231, 12519374, 712705, 10621198, 385025, 9761295,
        49152, 4211725, 4188400, 4130044]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint89Transport _ _
    monsterCo1GeometryVectorPoint89Transport_binary hc v

/-- Source point 89 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint89 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint89Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint89_binary :
    monsterCo1GeometryVectorPoint89.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint89Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint89Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
