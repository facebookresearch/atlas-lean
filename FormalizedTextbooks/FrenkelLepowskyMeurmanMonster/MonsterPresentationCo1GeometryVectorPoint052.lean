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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 52. -/
def monsterCo1GeometryVectorPoint52Transport : Co1 :=
  monsterCo1GeometryVectorPoint7Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint7Transport⁻¹ * monsterCo1GeometryVectorPoint18Transport

/-- Complete displayed binary matrix of actual transport 52. -/
def monsterCo1GeometryVectorPoint52Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    ![0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    ![0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    ![1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1]]

/-- First complete finite matrix product in literal actual transport 52. -/
def monsterCo1GeometryVectorPoint52AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    ![1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Second complete finite matrix product in literal actual transport 52. -/
def monsterCo1GeometryVectorPoint52AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 52 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint52Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint52Transport v =
      monsterCo1GeometryVectorPoint52Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint7Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8389632,
    4196352, 2802012, 4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 209091, 839730,
    2048, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint7InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 1378983, 1378987, 53522, 12611, 53794, 12931, 53250, 12291, 8437772,
    4194304, 49420, 49932, 16395, 32775, 78339, 315906, 143619, 577794, 196803, 786482,
    4196352, 8438796] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint18Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 5476570, 9495040] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint52AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129728, 2752832, 13965959, 13965963, 53520, 8402240, 53792, 8402560, 53248, 8401920,
    8389632, 4200448, 2801740, 4178124, 4217867, 4234247, 8468000, 315904, 8533264, 577792,
    210163, 839730, 6158, 50176] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint52AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![81, 274, 8389700, 8389704, 16, 1056, 64, 1152, 256, 1536, 1024, 51468, 4368, 8272,
    8405248, 8421632, 79171, 131072, 316690, 524288, 9445469, 2097152, 6996048, 8388608] := by
    decide +kernel
  have hc : monsterCo1GeometryVectorPoint52Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 8620261, 9495040] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint7Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint52AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5572775, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8389632,
    4196352, 2802012, 4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 209091, 839730,
    2048, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![4129728, 2752832, 13965959, 13965963, 53520, 8402240, 53792, 8402560, 53248, 8401920,
    8389632, 4200448, 2801740, 4178124, 4217867, 4234247, 8468000, 315904, 8533264, 577792,
    210163, 839730, 6158, 50176] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint52AfterSignMatrix *
    monsterCo1GeometryVectorPoint7InverseMatrix =
    monsterCo1GeometryVectorPoint52AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129728, 2752832, 13965959, 13965963, 53520, 8402240, 53792, 8402560, 53248, 8401920,
    8389632, 4200448, 2801740, 4178124, 4217867, 4234247, 8468000, 315904, 8533264, 577792,
    210163, 839730, 6158, 50176]
    ![4129776, 2752848, 1378983, 1378987, 53522, 12611, 53794, 12931, 53250, 12291, 8437772,
    4194304, 49420, 49932, 16395, 32775, 78339, 315906, 143619, 577794, 196803, 786482,
    4196352, 8438796]
    ![81, 274, 8389700, 8389704, 16, 1056, 64, 1152, 256, 1536, 1024, 51468, 4368, 8272,
    8405248, 8421632, 79171, 131072, 316690, 524288, 9445469, 2097152, 6996048, 8388608] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint52AfterInverseMatrix *
    monsterCo1GeometryVectorPoint18Matrix = monsterCo1GeometryVectorPoint52Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![81, 274, 8389700, 8389704, 16, 1056, 64, 1152, 256, 1536, 1024, 51468, 4368, 8272,
    8405248, 8421632, 79171, 131072, 316690, 524288, 9445469, 2097152, 6996048, 8388608]
    ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 5476570, 9495040]
    ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 8620261, 9495040] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint7Transport monsterCo1GeometryVectorPoint18Transport 1
    monsterCo1GeometryVectorPoint7Matrix monsterCo1GeometryVectorPoint7InverseMatrix
    monsterCo1GeometryVectorPoint18Matrix
    monsterCo1GeometryVectorPoint52AfterSignMatrix
    monsterCo1GeometryVectorPoint52AfterInverseMatrix monsterCo1GeometryVectorPoint52Matrix
    monsterCo1GeometryVectorPoint7Transport_binary
    monsterCo1GeometryVectorPoint7Transport_inverse_binary
    monsterCo1GeometryVectorPoint18Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 52. -/
def monsterCo1GeometryVectorPoint52InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0],
    ![1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint52Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint52Transport⁻¹ v =
      monsterCo1GeometryVectorPoint52InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint52Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758,
        12635279, 12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130,
        1593978, 13819448, 12384167, 1136156, 6568274, 8620261, 9495040] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint52InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![1008, 14989972, 14105085, 14191832, 8394014, 58449, 8450703, 57505, 8399334, 652,
        12579407, 12573891, 1377408, 12522174, 4130176, 4186481, 693112, 10638587, 337452,
        1373312, 49792, 8423916, 13898206, 4142659] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint52Matrix *
    monsterCo1GeometryVectorPoint52InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758,
        12635279, 12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130,
        1593978, 13819448, 12384167, 1136156, 6568274, 8620261, 9495040]
      ![1008, 14989972, 14105085, 14191832, 8394014, 58449, 8450703, 57505, 8399334, 652,
        12579407, 12573891, 1377408, 12522174, 4130176, 4186481, 693112, 10638587, 337452,
        1373312, 49792, 8423916, 13898206, 4142659]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint52Transport _ _
    monsterCo1GeometryVectorPoint52Transport_binary hc v

/-- Source point 52 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint52 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint52Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint52_binary :
    monsterCo1GeometryVectorPoint52.val =
      ![1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint52Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint52Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
