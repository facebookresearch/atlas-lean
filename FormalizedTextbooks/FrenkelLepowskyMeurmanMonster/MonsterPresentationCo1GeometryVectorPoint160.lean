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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 160. -/
def monsterCo1GeometryVectorPoint160Transport : Co1 :=
  monsterCo1GeometryVectorPoint90Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint90Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 160. -/
def monsterCo1GeometryVectorPoint160Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
      1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
      5778990, 10300013, 3171169, 3337371, 8388848]

/-- First complete finite matrix product in literal actual transport 160. -/
def monsterCo1GeometryVectorPoint160AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
      12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
      1151952, 15011355, 14146247, 8389632]

/-- Second complete finite matrix product in literal actual transport 160. -/
def monsterCo1GeometryVectorPoint160AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
      6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
      14209311, 2138560, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 160 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint160Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint160Transport v =
      monsterCo1GeometryVectorPoint160Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint90Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint90InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
    15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152, 4211725,
    1436211, 1727] := by rfl
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint160AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
    12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
    1151952, 15011355, 14146247, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint160AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
    6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
    14209311, 2138560, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint160Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint90Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint160AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 34736, 8431168, 1456, 8451136, 8450048, 8443488, 8401568, 8419296, 37712, 8405968,
    12911104, 5242626, 13942621, 16250893, 15202433, 4389892, 5856880, 1179781, 16636811,
    1151952, 15011355, 14146247, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint160AfterSignMatrix *
    monsterCo1GeometryVectorPoint90InverseMatrix =
    monsterCo1GeometryVectorPoint160AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint160AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint160Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![556, 8390074, 8389580, 1719, 16, 32, 143, 685, 8389127, 8389978, 8389525, 7367598,
    6062916, 11837976, 14471841, 11301666, 6398754, 9089180, 2114817, 13428004, 14706393,
    14209311, 2138560, 8388608]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint90Transport monsterCo1GeometryVectorPoint154Transport 5
    monsterCo1GeometryVectorPoint90Matrix monsterCo1GeometryVectorPoint90InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint160AfterSignMatrix
    monsterCo1GeometryVectorPoint160AfterInverseMatrix monsterCo1GeometryVectorPoint160Matrix
    monsterCo1GeometryVectorPoint90Transport_binary
    monsterCo1GeometryVectorPoint90Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 160 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint160 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint160Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint160_binary :
    monsterCo1GeometryVectorPoint160.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint160Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint160Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
