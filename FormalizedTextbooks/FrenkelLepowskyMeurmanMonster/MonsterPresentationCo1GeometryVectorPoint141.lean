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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint095

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 141. -/
def monsterCo1GeometryVectorPoint141Transport : Co1 :=
  monsterCo1GeometryVectorPoint81Transport * monsterCo1GeometryTransportOperator 3 *
    monsterCo1GeometryVectorPoint81Transport⁻¹ * monsterCo1GeometryVectorPoint95Transport

/-- Complete displayed binary matrix of actual transport 141. -/
def monsterCo1GeometryVectorPoint141Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
      12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
      7536505, 9228374, 12696754, 3463037, 387244, 58368]

/-- First complete finite matrix product in literal actual transport 141. -/
def monsterCo1GeometryVectorPoint141AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 8394496, 8393984, 57504, 58400, 57456, 57584, 26272, 25408, 8388784,
      1215170, 8859748, 8413190, 10494444, 2138459, 5336005, 12950858, 13604954, 5971245,
      9479581, 9461969, 9577781, 8389632]

/-- Second complete finite matrix product in literal actual transport 141. -/
def monsterCo1GeometryVectorPoint141AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3197181, 8393472, 8432,
      8406160, 8422496, 8454854, 8520138, 8651322, 8913206, 1049761, 2098257, 4195084, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 141 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint141Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint141Transport v =
      monsterCo1GeometryVectorPoint141Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint81InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57569, 4138783, 12518114, 9372008, 241, 8389825, 97, 192, 8390544, 12, 240, 15731814,
    8390552, 106, 1431, 8389100, 4994232, 14615336, 2893264, 5834569, 10543597, 3163248,
    10631990, 8388848] := by rfl
  have hy : monsterCo1GeometryVectorPoint95Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 9861848, 6212328, 13969570, 11882189, 10874621, 4455428, 14203509,
    9581094, 8134568, 5332530, 10801501, 1436173, 58368] := by rfl
  have he : monsterCo1GeometryVectorPoint141AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 8394496, 8393984, 57504, 58400, 57456, 57584, 26272, 25408, 8388784,
    1215170, 8859748, 8413190, 10494444, 2138459, 5336005, 12950858, 13604954, 5971245,
    9479581, 9461969, 9577781, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint141AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3197181, 8393472, 8432,
    8406160, 8422496, 8454854, 8520138, 8651322, 8913206, 1049761, 2098257, 4195084, 8388608]
    := by rfl
  have hc : monsterCo1GeometryVectorPoint141Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
    12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
    7536505, 9228374, 12696754, 3463037, 387244, 58368] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint81Matrix *
    monsterCo1GeometryTransportOperatorMatrix 3 =
    monsterCo1GeometryVectorPoint141AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 3)
    ![1040, 13648, 8394496, 8393984, 57504, 58400, 57456, 57584, 26272, 25408, 8388784,
    1215170, 8859748, 8413190, 10494444, 2138459, 5336005, 12950858, 13604954, 5971245,
    9479581, 9461969, 9577781, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 3) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint141AfterSignMatrix *
    monsterCo1GeometryVectorPoint81InverseMatrix =
    monsterCo1GeometryVectorPoint141AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1040, 13648, 8394496, 8393984, 57504, 58400, 57456, 57584, 26272, 25408, 8388784,
    1215170, 8859748, 8413190, 10494444, 2138459, 5336005, 12950858, 13604954, 5971245,
    9479581, 9461969, 9577781, 8389632]
    ![57569, 4138783, 12518114, 9372008, 241, 8389825, 97, 192, 8390544, 12, 240, 15731814,
    8390552, 106, 1431, 8389100, 4994232, 14615336, 2893264, 5834569, 10543597, 3163248,
    10631990, 8388848]
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3197181, 8393472, 8432,
    8406160, 8422496, 8454854, 8520138, 8651322, 8913206, 1049761, 2098257, 4195084, 8388608]
    he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint141AfterInverseMatrix *
    monsterCo1GeometryVectorPoint95Matrix = monsterCo1GeometryVectorPoint141Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3197181, 8393472, 8432,
    8406160, 8422496, 8454854, 8520138, 8651322, 8913206, 1049761, 2098257, 4195084, 8388608]
    ![49312, 8414416, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 9861848, 6212328, 13969570, 11882189, 10874621, 4455428, 14203509,
    9581094, 8134568, 5332530, 10801501, 1436173, 58368]
    ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
    12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
    7536505, 9228374, 12696754, 3463037, 387244, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint81Transport monsterCo1GeometryVectorPoint95Transport 3
    monsterCo1GeometryVectorPoint81Matrix monsterCo1GeometryVectorPoint81InverseMatrix
    monsterCo1GeometryVectorPoint95Matrix
    monsterCo1GeometryVectorPoint141AfterSignMatrix
    monsterCo1GeometryVectorPoint141AfterInverseMatrix monsterCo1GeometryVectorPoint141Matrix
    monsterCo1GeometryVectorPoint81Transport_binary
    monsterCo1GeometryVectorPoint81Transport_inverse_binary
    monsterCo1GeometryVectorPoint95Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 141. -/
def monsterCo1GeometryVectorPoint141InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 16657741, 13450966, 4382706, 8389918, 8388689, 1679, 161, 4211323, 8438396,
      12517699, 8380818, 9765489, 12517810, 12519052, 4130429, 713684, 2234224, 385745,
      9762068, 8438384, 12599921, 928599, 4130127]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint141Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint141Transport⁻¹ v =
      monsterCo1GeometryVectorPoint141InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint141Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
        12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
        7536505, 9228374, 12696754, 3463037, 387244, 58368] := by rfl
  have hmi : monsterCo1GeometryVectorPoint141InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![8389616, 16657741, 13450966, 4382706, 8389918, 8388689, 1679, 161, 4211323, 8438396,
        12517699, 8380818, 9765489, 12517810, 12519052, 4130429, 713684, 2234224, 385745,
        9762068, 8438384, 12599921, 928599, 4130127] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint141Matrix *
    monsterCo1GeometryVectorPoint141InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
        12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
        7536505, 9228374, 12696754, 3463037, 387244, 58368]
      ![8389616, 16657741, 13450966, 4382706, 8389918, 8388689, 1679, 161, 4211323, 8438396,
        12517699, 8380818, 9765489, 12517810, 12519052, 4130429, 713684, 2234224, 385745,
        9762068, 8438384, 12599921, 928599, 4130127]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint141Transport _ _
    monsterCo1GeometryVectorPoint141Transport_binary hc v

/-- Source point 141 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint141 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint141Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint141_binary :
    monsterCo1GeometryVectorPoint141.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint141Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint141Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
