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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 75. -/
def monsterCo1GeometryVectorPoint75Transport : Co1 :=
  monsterCo1GeometryVectorPoint27Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint27Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 75. -/
def monsterCo1GeometryVectorPoint75Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
      1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
      9478477, 9461761, 9825104, 8388784]

/-- First complete finite matrix product in literal actual transport 75. -/
def monsterCo1GeometryVectorPoint75AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58545, 12766656, 7531291, 6482397, 57344, 8445984, 57552, 57424, 33280, 8405984, 8389632,
      4709079, 13769942, 9437383, 10486860, 11535498, 12689060, 12607335, 4890422, 13524432,
      9480173, 9463457, 14018033, 8446992]

/-- Second complete finite matrix product in literal actual transport 75. -/
def monsterCo1GeometryVectorPoint75AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 1935608, 855300, 2959592, 58609, 8389680, 58529, 58465, 8397229, 8421847, 1024,
      3284301, 12393072, 2098656, 11552624, 9478800, 2307021, 2075719, 11119415, 3517722,
      11551446, 349, 13588646, 8447201]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 75 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint75Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint75Transport v =
      monsterCo1GeometryVectorPoint75Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint27Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
    8405104, 8389632, 12966029, 5250063, 9437185, 10486784, 11535360, 4430948, 4349160,
    13147381, 13392985, 1090731, 1074343, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint27InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 1040128, 11533984, 10485072, 8389648, 48, 8389760, 192, 18187, 49164, 8447217,
    16770254, 8401859, 59137, 8446545, 8446369, 3342528, 2234224, 3932400, 9761632, 49152,
    17408, 4210685, 8446193] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint75AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58545, 12766656, 7531291, 6482397, 57344, 8445984, 57552, 57424, 33280, 8405984, 8389632,
    4709079, 13769942, 9437383, 10486860, 11535498, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 14018033, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint75AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 1935608, 855300, 2959592, 58609, 8389680, 58529, 58465, 8397229, 8421847, 1024,
    3284301, 12393072, 2098656, 11552624, 9478800, 2307021, 2075719, 11119415, 3517722,
    11551446, 349, 13588646, 8447201] := by rfl
  have hc : monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint27Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint75AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58529, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
    8405104, 8389632, 12966029, 5250063, 9437185, 10486784, 11535360, 4430948, 4349160,
    13147381, 13392985, 1090731, 1074343, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![58545, 12766656, 7531291, 6482397, 57344, 8445984, 57552, 57424, 33280, 8405984, 8389632,
    4709079, 13769942, 9437383, 10486860, 11535498, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 14018033, 8446992] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint75AfterSignMatrix *
    monsterCo1GeometryVectorPoint27InverseMatrix =
    monsterCo1GeometryVectorPoint75AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58545, 12766656, 7531291, 6482397, 57344, 8445984, 57552, 57424, 33280, 8405984, 8389632,
    4709079, 13769942, 9437383, 10486860, 11535498, 12689060, 12607335, 4890422, 13524432,
    9480173, 9463457, 14018033, 8446992]
    ![8388849, 1040128, 11533984, 10485072, 8389648, 48, 8389760, 192, 18187, 49164, 8447217,
    16770254, 8401859, 59137, 8446545, 8446369, 3342528, 2234224, 3932400, 9761632, 49152,
    17408, 4210685, 8446193]
    ![8389649, 1935608, 855300, 2959592, 58609, 8389680, 58529, 58465, 8397229, 8421847, 1024,
    3284301, 12393072, 2098656, 11552624, 9478800, 2307021, 2075719, 11119415, 3517722,
    11551446, 349, 13588646, 8447201] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint75AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint75Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8389649, 1935608, 855300, 2959592, 58609, 8389680, 58529, 58465, 8397229, 8421847, 1024,
    3284301, 12393072, 2098656, 11552624, 9478800, 2307021, 2075719, 11119415, 3517722,
    11551446, 349, 13588646, 8447201]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint27Transport monsterCo1GeometryVectorPoint35Transport 6
    monsterCo1GeometryVectorPoint27Matrix monsterCo1GeometryVectorPoint27InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint75AfterSignMatrix
    monsterCo1GeometryVectorPoint75AfterInverseMatrix monsterCo1GeometryVectorPoint75Matrix
    monsterCo1GeometryVectorPoint27Transport_binary
    monsterCo1GeometryVectorPoint27Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- Source point 75 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint75 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint75Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint75_binary :
    monsterCo1GeometryVectorPoint75.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint75Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint75Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
