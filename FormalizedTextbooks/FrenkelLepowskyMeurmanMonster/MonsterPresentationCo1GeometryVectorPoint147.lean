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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint047
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint102

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 147. -/
def monsterCo1GeometryVectorPoint147Transport : Co1 :=
  monsterCo1GeometryVectorPoint47Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint47Transport⁻¹ * monsterCo1GeometryVectorPoint102Transport

/-- Complete displayed binary matrix of actual transport 147. -/
def monsterCo1GeometryVectorPoint147Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
      10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
      9462746, 12455383, 7432975, 1073856, 13031540, 1200]

/-- First complete finite matrix product in literal actual transport 147. -/
def monsterCo1GeometryVectorPoint147AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 11567350, 10519162, 4278688, 12667345, 12676992, 12684145, 12701184,
      4270721, 9438860, 5730055, 14666238, 12897793, 5612706, 13961042, 8647733, 9982000,
      13884436, 12383979, 9525072, 15022363, 5629058, 8447008]

/-- Second complete finite matrix product in literal actual transport 147. -/
def monsterCo1GeometryVectorPoint147AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 12616113, 7574623, 16545238, 6180600, 14765195, 6393499, 14781962, 2214936,
      2018570, 9430405, 4892858, 4613424, 11456188, 4243938, 12533858, 9825795, 8467471,
      114828, 13083206, 6332421, 858258, 8372275, 12517906]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 147 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint147Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint147Transport v =
      monsterCo1GeometryVectorPoint147Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint47Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint47InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792, 12518991,
    8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189, 9760911, 49804,
    12600807, 13897182, 12517955] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint102Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12742900, 8902496, 3429399, 2618391, 13064409, 4677242, 338639, 338511, 12618749,
    12617790, 9676503, 5450516, 8873588, 8818904, 8616308, 8616820, 8842133, 466230, 13584682,
    13117673, 477283, 428259, 8662179, 480471] := by rfl
  have he : monsterCo1GeometryVectorPoint147AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 11567350, 10519162, 4278688, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 5730055, 14666238, 12897793, 5612706, 13961042, 8647733, 9982000,
    13884436, 12383979, 9525072, 15022363, 5629058, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint147AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 12616113, 7574623, 16545238, 6180600, 14765195, 6393499, 14781962, 2214936,
    2018570, 9430405, 4892858, 4613424, 11456188, 4243938, 12533858, 9825795, 8467471, 114828,
    13083206, 6332421, 858258, 8372275, 12517906] := by rfl
  have hc : monsterCo1GeometryVectorPoint147Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
    10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
    9462746, 12455383, 7432975, 1073856, 13031540, 1200] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint47Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint147AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 8422320, 11567350, 10519162, 4278688, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 5730055, 14666238, 12897793, 5612706, 13961042, 8647733, 9982000,
    13884436, 12383979, 9525072, 15022363, 5629058, 8447008] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint147AfterSignMatrix *
    monsterCo1GeometryVectorPoint47InverseMatrix =
    monsterCo1GeometryVectorPoint147AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 8422320, 11567350, 10519162, 4278688, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 5730055, 14666238, 12897793, 5612706, 13961042, 8647733, 9982000,
    13884436, 12383979, 9525072, 15022363, 5629058, 8447008]
    ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792, 12518991,
    8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189, 9760911, 49804,
    12600807, 13897182, 12517955]
    ![49696, 12616113, 7574623, 16545238, 6180600, 14765195, 6393499, 14781962, 2214936,
    2018570, 9430405, 4892858, 4613424, 11456188, 4243938, 12533858, 9825795, 8467471, 114828,
    13083206, 6332421, 858258, 8372275, 12517906] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint147AfterInverseMatrix *
    monsterCo1GeometryVectorPoint102Matrix = monsterCo1GeometryVectorPoint147Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 12616113, 7574623, 16545238, 6180600, 14765195, 6393499, 14781962, 2214936,
    2018570, 9430405, 4892858, 4613424, 11456188, 4243938, 12533858, 9825795, 8467471, 114828,
    13083206, 6332421, 858258, 8372275, 12517906]
    ![12742900, 8902496, 3429399, 2618391, 13064409, 4677242, 338639, 338511, 12618749,
    12617790, 9676503, 5450516, 8873588, 8818904, 8616308, 8616820, 8842133, 466230, 13584682,
    13117673, 477283, 428259, 8662179, 480471]
    ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
    10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
    9462746, 12455383, 7432975, 1073856, 13031540, 1200] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint47Transport monsterCo1GeometryVectorPoint102Transport 5
    monsterCo1GeometryVectorPoint47Matrix monsterCo1GeometryVectorPoint47InverseMatrix
    monsterCo1GeometryVectorPoint102Matrix
    monsterCo1GeometryVectorPoint147AfterSignMatrix
    monsterCo1GeometryVectorPoint147AfterInverseMatrix monsterCo1GeometryVectorPoint147Matrix
    monsterCo1GeometryVectorPoint47Transport_binary
    monsterCo1GeometryVectorPoint47Transport_inverse_binary
    monsterCo1GeometryVectorPoint102Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 147. -/
def monsterCo1GeometryVectorPoint147InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![15168521, 4227943, 14186344, 8647737, 6779170, 6780059, 6780078, 8388753, 8389571,
      16744832, 1320, 7419103, 16179616, 11567577, 11040172, 16744817, 12209371, 5942320,
      16709318, 6941439, 2097610, 15401811, 9140372, 1471]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint147Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint147Transport⁻¹ v =
      monsterCo1GeometryVectorPoint147InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint147Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
        10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
        9462746, 12455383, 7432975, 1073856, 13031540, 1200] := by rfl
  have hmi : monsterCo1GeometryVectorPoint147InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![15168521, 4227943, 14186344, 8647737, 6779170, 6780059, 6780078, 8388753, 8389571,
        16744832, 1320, 7419103, 16179616, 11567577, 11040172, 16744817, 12209371, 5942320,
        16709318, 6941439, 2097610, 15401811, 9140372, 1471] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint147Matrix *
    monsterCo1GeometryVectorPoint147InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
        10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
        9462746, 12455383, 7432975, 1073856, 13031540, 1200]
      ![15168521, 4227943, 14186344, 8647737, 6779170, 6780059, 6780078, 8388753, 8389571,
        16744832, 1320, 7419103, 16179616, 11567577, 11040172, 16744817, 12209371, 5942320,
        16709318, 6941439, 2097610, 15401811, 9140372, 1471]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint147Transport _ _
    monsterCo1GeometryVectorPoint147Transport_binary hc v

/-- Source point 147 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint147 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint147Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint147_binary :
    monsterCo1GeometryVectorPoint147.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint147Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint147Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
