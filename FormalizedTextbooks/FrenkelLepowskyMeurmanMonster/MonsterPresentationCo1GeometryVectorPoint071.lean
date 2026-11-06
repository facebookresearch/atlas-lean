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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint034

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 71. -/
def monsterCo1GeometryVectorPoint71Transport : Co1 :=
  monsterCo1GeometryVectorPoint13Transport * monsterCo1GeometryTransportOperator 3 *
    monsterCo1GeometryVectorPoint13Transport⁻¹ * monsterCo1GeometryVectorPoint34Transport

/-- Complete displayed binary matrix of actual transport 71. -/
def monsterCo1GeometryVectorPoint71Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760, 5620396,
      11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623, 258639, 7580521,
      5520044, 8389632]

/-- First complete finite matrix product in literal actual transport 71. -/
def monsterCo1GeometryVectorPoint71AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 13978279, 5589675, 8392976, 12608, 53792, 12928, 53248, 12288, 8389632,
      13924684, 11154716, 12531516, 12634603, 12586855, 78816, 9556796, 8520348, 16218247,
      8585279, 7568009, 18443, 8437760]

/-- Second complete finite matrix product in literal actual transport 71. -/
def monsterCo1GeometryVectorPoint71AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8445984, 8442528, 46560, 8418144, 1040, 32, 64, 128, 256, 512, 1024, 48132, 1070, 1709,
      8390123, 1895, 66016, 194463, 312604, 550198, 1099004, 2138154, 12667375, 8389632]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 71 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint71Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint71Transport v =
      monsterCo1GeometryVectorPoint71Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint13Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint13InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint34Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5622951, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8437760,
    18443, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 209587, 840146,
    4194315, 50176] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint71AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 13978279, 5589675, 8392976, 12608, 53792, 12928, 53248, 12288, 8389632,
    13924684, 11154716, 12531516, 12634603, 12586855, 78816, 9556796, 8520348, 16218247,
    8585279, 7568009, 18443, 8437760] := by rfl
  have hf : monsterCo1GeometryVectorPoint71AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8445984, 8442528, 46560, 8418144, 1040, 32, 64, 128, 256, 512, 1024, 48132, 1070, 1709,
    8390123, 1895, 66016, 194463, 312604, 550198, 1099004, 2138154, 12667375, 8389632] := by rfl
  have hc : monsterCo1GeometryVectorPoint71Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760, 5620396,
    11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623, 258639, 7580521,
    5520044, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint13Matrix *
    monsterCo1GeometryTransportOperatorMatrix 3 =
    monsterCo1GeometryVectorPoint71AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 3)
    ![4129776, 2752848, 13978279, 5589675, 8392976, 12608, 53792, 12928, 53248, 12288, 8389632,
    13924684, 11154716, 12531516, 12634603, 12586855, 78816, 9556796, 8520348, 16218247,
    8585279, 7568009, 18443, 8437760] hx (monsterCo1GeometryBinaryOperatorMasks_decode 3) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint71AfterSignMatrix *
    monsterCo1GeometryVectorPoint13InverseMatrix =
    monsterCo1GeometryVectorPoint71AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129776, 2752848, 13978279, 5589675, 8392976, 12608, 53792, 12928, 53248, 12288, 8389632,
    13924684, 11154716, 12531516, 12634603, 12586855, 78816, 9556796, 8520348, 16218247,
    8585279, 7568009, 18443, 8437760]
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436]
    ![8445984, 8442528, 46560, 8418144, 1040, 32, 64, 128, 256, 512, 1024, 48132, 1070, 1709,
    8390123, 1895, 66016, 194463, 312604, 550198, 1099004, 2138154, 12667375, 8389632] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint71AfterInverseMatrix *
    monsterCo1GeometryVectorPoint34Matrix = monsterCo1GeometryVectorPoint71Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8445984, 8442528, 46560, 8418144, 1040, 32, 64, 128, 256, 512, 1024, 48132, 1070, 1709,
    8390123, 1895, 66016, 194463, 312604, 550198, 1099004, 2138154, 12667375, 8389632]
    ![4129008, 2752592, 5622951, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8437760,
    18443, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 209587, 840146,
    4194315, 50176]
    ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760, 5620396,
    11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623, 258639, 7580521,
    5520044, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint13Transport monsterCo1GeometryVectorPoint34Transport 3
    monsterCo1GeometryVectorPoint13Matrix monsterCo1GeometryVectorPoint13InverseMatrix
    monsterCo1GeometryVectorPoint34Matrix
    monsterCo1GeometryVectorPoint71AfterSignMatrix
    monsterCo1GeometryVectorPoint71AfterInverseMatrix monsterCo1GeometryVectorPoint71Matrix
    monsterCo1GeometryVectorPoint13Transport_binary
    monsterCo1GeometryVectorPoint13Transport_inverse_binary
    monsterCo1GeometryVectorPoint34Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 71. -/
def monsterCo1GeometryVectorPoint71InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4142451, 2766803, 13922752, 13939520, 8389554, 963, 8389762, 3, 8390306, 643, 8390284,
      4261903, 908, 396, 8390123, 8390503, 65667, 8701486, 193420, 8938724, 246351, 9205594,
      63503, 1676]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint71Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint71Transport⁻¹ v =
      monsterCo1GeometryVectorPoint71InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint71Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760,
        5620396, 11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623,
        258639, 7580521, 5520044, 8389632] := by rfl
  have hmi : monsterCo1GeometryVectorPoint71InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![4142451, 2766803, 13922752, 13939520, 8389554, 963, 8389762, 3, 8390306, 643, 8390284,
        4261903, 908, 396, 8390123, 8390503, 65667, 8701486, 193420, 8938724, 246351, 9205594,
        63503, 1676] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint71Matrix *
    monsterCo1GeometryVectorPoint71InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760,
        5620396, 11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623,
        258639, 7580521, 5520044, 8389632]
      ![4142451, 2766803, 13922752, 13939520, 8389554, 963, 8389762, 3, 8390306, 643, 8390284,
        4261903, 908, 396, 8390123, 8390503, 65667, 8701486, 193420, 8938724, 246351, 9205594,
        63503, 1676]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint71Transport _ _
    monsterCo1GeometryVectorPoint71Transport_binary hc v

/-- Source point 71 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint71 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint71Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint71_binary :
    monsterCo1GeometryVectorPoint71.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint71Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint71Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
