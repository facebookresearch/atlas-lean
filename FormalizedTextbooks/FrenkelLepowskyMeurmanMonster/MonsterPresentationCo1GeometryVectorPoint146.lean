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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint101

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 146. -/
def monsterCo1GeometryVectorPoint146Transport : Co1 :=
  monsterCo1GeometryVectorPoint90Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint90Transport⁻¹ * monsterCo1GeometryVectorPoint101Transport

/-- Complete displayed binary matrix of actual transport 146. -/
def monsterCo1GeometryVectorPoint146Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371, 2114365,
      2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484, 6005326,
      8105472, 9690902, 9495761, 8586102, 1200]

/-- First complete finite matrix product in literal actual transport 146. -/
def monsterCo1GeometryVectorPoint146AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
      12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
      1151952, 15011355, 14146247, 8389632]

/-- Second complete finite matrix product in literal actual transport 146. -/
def monsterCo1GeometryVectorPoint146AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
      6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
      14209311, 2138560, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 146 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint146Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint146Transport v =
      monsterCo1GeometryVectorPoint146Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint90Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint90InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
    15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152, 4211725,
    1436211, 1727] := by rfl
  have hy : monsterCo1GeometryVectorPoint101Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10974526, 8902163, 2617657, 2619230, 10983048, 2147580, 58432, 505091, 10503547,
    10949231, 8868211, 7799467, 1361300, 7107841, 14765428, 7531587, 267950, 8123139, 13759254,
    5359413, 4546086, 3837452, 2386792, 1200] := by rfl
  have he : monsterCo1GeometryVectorPoint146AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
    12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
    1151952, 15011355, 14146247, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint146AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
    6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
    14209311, 2138560, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint146Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371, 2114365,
    2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484, 6005326, 8105472,
    9690902, 9495761, 8586102, 1200] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint90Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint146AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
    12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
    1151952, 15011355, 14146247, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint146AfterSignMatrix *
    monsterCo1GeometryVectorPoint90InverseMatrix =
    monsterCo1GeometryVectorPoint146AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
    12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
    1151952, 15011355, 14146247, 8389632]
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
    15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152, 4211725,
    1436211, 1727]
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
    6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
    14209311, 2138560, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint146AfterInverseMatrix *
    monsterCo1GeometryVectorPoint101Matrix = monsterCo1GeometryVectorPoint146Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
    6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
    14209311, 2138560, 8388608]
    ![10974526, 8902163, 2617657, 2619230, 10983048, 2147580, 58432, 505091, 10503547,
    10949231, 8868211, 7799467, 1361300, 7107841, 14765428, 7531587, 267950, 8123139, 13759254,
    5359413, 4546086, 3837452, 2386792, 1200]
    ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371, 2114365,
    2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484, 6005326, 8105472,
    9690902, 9495761, 8586102, 1200] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint90Transport monsterCo1GeometryVectorPoint101Transport 5
    monsterCo1GeometryVectorPoint90Matrix monsterCo1GeometryVectorPoint90InverseMatrix
    monsterCo1GeometryVectorPoint101Matrix
    monsterCo1GeometryVectorPoint146AfterSignMatrix
    monsterCo1GeometryVectorPoint146AfterInverseMatrix monsterCo1GeometryVectorPoint146Matrix
    monsterCo1GeometryVectorPoint90Transport_binary
    monsterCo1GeometryVectorPoint90Transport_inverse_binary
    monsterCo1GeometryVectorPoint101Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 146. -/
def monsterCo1GeometryVectorPoint146InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![13480196, 12616405, 15905574, 4436931, 5092815, 13481419, 13479954, 192, 963, 8355985,
      196, 1152827, 12354075, 9479507, 2266474, 8355936, 2268982, 6462514, 2004567, 1800748,
      10487095, 10593757, 13888415, 435]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint146Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint146Transport⁻¹ v =
      monsterCo1GeometryVectorPoint146InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint146Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371,
        2114365, 2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484,
        6005326, 8105472, 9690902, 9495761, 8586102, 1200] := by rfl
  have hmi : monsterCo1GeometryVectorPoint146InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![13480196, 12616405, 15905574, 4436931, 5092815, 13481419, 13479954, 192, 963, 8355985,
        196, 1152827, 12354075, 9479507, 2266474, 8355936, 2268982, 6462514, 2004567, 1800748,
        10487095, 10593757, 13888415, 435] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint146Matrix *
    monsterCo1GeometryVectorPoint146InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371,
        2114365, 2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484,
        6005326, 8105472, 9690902, 9495761, 8586102, 1200]
      ![13480196, 12616405, 15905574, 4436931, 5092815, 13481419, 13479954, 192, 963, 8355985,
        196, 1152827, 12354075, 9479507, 2266474, 8355936, 2268982, 6462514, 2004567, 1800748,
        10487095, 10593757, 13888415, 435]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint146Transport _ _
    monsterCo1GeometryVectorPoint146Transport_binary hc v

/-- Source point 146 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint146 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint146Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint146_binary :
    monsterCo1GeometryVectorPoint146.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint146Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint146Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
