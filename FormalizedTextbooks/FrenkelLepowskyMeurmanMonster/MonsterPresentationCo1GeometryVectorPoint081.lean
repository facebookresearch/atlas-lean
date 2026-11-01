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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 81. -/
def monsterCo1GeometryVectorPoint81Transport : Co1 :=
  monsterCo1GeometryVectorPoint25Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint25Transport⁻¹ * monsterCo1GeometryVectorPoint36Transport

/-- Complete displayed binary matrix of actual transport 81. -/
def monsterCo1GeometryVectorPoint81Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
      471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053,
      1074337, 9577173, 8389632]

/-- First complete finite matrix product in literal actual transport 81. -/
def monsterCo1GeometryVectorPoint81AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447152, 53712, 8450944, 8450432, 57344, 8445984, 57552, 57424, 33280, 8405984, 57360,
      9584422, 13815558, 1107575, 10535084, 11584106, 12689060, 12607335, 4890422, 13524432,
      9480173, 9463457, 4709079, 8389632]

/-- Second complete finite matrix product in literal actual transport 81. -/
def monsterCo1GeometryVectorPoint81AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1041, 1896, 4, 8, 8388849, 1072, 8388769, 8388705, 8390061, 8390103, 8389857, 8195563,
      16584986, 10487293, 3163146, 9479655, 2298819, 14622794, 15279930, 16056602, 11544283,
      8528, 15872334, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 81 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint81Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint81Transport v =
      monsterCo1GeometryVectorPoint81Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint25Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447136, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 1064623, 13684367, 1107617, 2146720, 3195808, 4430948, 4349160, 13147381,
    13392985, 1090731, 1074343, 12966029, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint25InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447216, 13619970, 7337647, 6288735, 1040, 48, 1152, 192, 8389387, 12, 1265, 8387777,
    8390595, 8389377, 8390225, 8390049, 3342528, 10621822, 3932400, 9762671, 49164, 8405003,
    8395763, 8389873] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint81AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447152, 53712, 8450944, 8450432, 57344, 8445984, 57552, 57424, 33280, 8405984, 57360,
    9584422, 13815558, 1107575, 10535084, 11584106, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 4709079, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint81AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 1896, 4, 8, 8388849, 1072, 8388769, 8388705, 8390061, 8390103, 8389857, 8195563,
    16584986, 10487293, 3163146, 9479655, 2298819, 14622794, 15279930, 16056602, 11544283,
    8528, 15872334, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint25Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint81AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447136, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 1064623, 13684367, 1107617, 2146720, 3195808, 4430948, 4349160, 13147381,
    13392985, 1090731, 1074343, 12966029, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8447152, 53712, 8450944, 8450432, 57344, 8445984, 57552, 57424, 33280, 8405984, 57360,
    9584422, 13815558, 1107575, 10535084, 11584106, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 4709079, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint81AfterSignMatrix *
    monsterCo1GeometryVectorPoint25InverseMatrix =
    monsterCo1GeometryVectorPoint81AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447152, 53712, 8450944, 8450432, 57344, 8445984, 57552, 57424, 33280, 8405984, 57360,
    9584422, 13815558, 1107575, 10535084, 11584106, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 4709079, 8389632]
    ![8447216, 13619970, 7337647, 6288735, 1040, 48, 1152, 192, 8389387, 12, 1265, 8387777,
    8390595, 8389377, 8390225, 8390049, 3342528, 10621822, 3932400, 9762671, 49164, 8405003,
    8395763, 8389873]
    ![1041, 1896, 4, 8, 8388849, 1072, 8388769, 8388705, 8390061, 8390103, 8389857, 8195563,
    16584986, 10487293, 3163146, 9479655, 2298819, 14622794, 15279930, 16056602, 11544283,
    8528, 15872334, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint81AfterInverseMatrix *
    monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryVectorPoint81Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1041, 1896, 4, 8, 8388849, 1072, 8388769, 8388705, 8390061, 8390103, 8389857, 8195563,
    16584986, 10487293, 3163146, 9479655, 2298819, 14622794, 15279930, 16056602, 11544283,
    8528, 15872334, 8388608]
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632]
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint25Transport monsterCo1GeometryVectorPoint36Transport 6
    monsterCo1GeometryVectorPoint25Matrix monsterCo1GeometryVectorPoint25InverseMatrix
    monsterCo1GeometryVectorPoint36Matrix
    monsterCo1GeometryVectorPoint81AfterSignMatrix
    monsterCo1GeometryVectorPoint81AfterInverseMatrix monsterCo1GeometryVectorPoint81Matrix
    monsterCo1GeometryVectorPoint25Transport_binary
    monsterCo1GeometryVectorPoint25Transport_inverse_binary
    monsterCo1GeometryVectorPoint36Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 81. -/
def monsterCo1GeometryVectorPoint81InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57569, 4138783, 12518114, 9372008, 241, 8389825, 97, 192, 8390544, 12, 240, 15731814,
      8390552, 106, 1431, 8389100, 4994232, 14615336, 2893264, 5834569, 10543597, 3163248,
      10631990, 8388848]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint81Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint81Transport⁻¹ v =
      monsterCo1GeometryVectorPoint81InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784,
        9620777, 471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653,
        1091053, 1074337, 9577173, 8389632] := by rfl
  have hmi : monsterCo1GeometryVectorPoint81InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![57569, 4138783, 12518114, 9372008, 241, 8389825, 97, 192, 8390544, 12, 240, 15731814,
        8390552, 106, 1431, 8389100, 4994232, 14615336, 2893264, 5834569, 10543597, 3163248,
        10631990, 8388848] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint81Matrix *
    monsterCo1GeometryVectorPoint81InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784,
        9620777, 471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653,
        1091053, 1074337, 9577173, 8389632]
      ![57569, 4138783, 12518114, 9372008, 241, 8389825, 97, 192, 8390544, 12, 240, 15731814,
        8390552, 106, 1431, 8389100, 4994232, 14615336, 2893264, 5834569, 10543597, 3163248,
        10631990, 8388848]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint81Transport _ _
    monsterCo1GeometryVectorPoint81Transport_binary hc v

/-- Source point 81 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint81 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint81Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint81_binary :
    monsterCo1GeometryVectorPoint81.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint81Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint81Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
