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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint056
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint058

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 106. -/
def monsterCo1GeometryVectorPoint106Transport : Co1 :=
  monsterCo1GeometryVectorPoint56Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint56Transport⁻¹ * monsterCo1GeometryVectorPoint58Transport

/-- Complete displayed binary matrix of actual transport 106. -/
def monsterCo1GeometryVectorPoint106Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388785, 4242575, 15743102, 14702702, 8389648, 48, 58560, 58432, 34000, 17520, 8389632,
      9748655, 5303871, 9479681, 2122080, 3195728, 1255002, 1183958, 7875956, 7137816, 3179898,
      2154502, 8911477, 8445952]

/-- First complete finite matrix product in literal actual transport 106. -/
def monsterCo1GeometryVectorPoint106AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 4233231, 7355646, 6315246, 16, 58416, 192, 64, 24784, 41072, 58368, 12583438,
      8451600, 8413696, 49648, 41952, 13888116, 131286, 11060635, 1860294, 11577339, 1073686,
      4388055, 8445952]

/-- Second complete finite matrix product in literal actual transport 106. -/
def monsterCo1GeometryVectorPoint106AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8442194, 8434580, 8418008, 16, 8389664, 64, 128, 256, 512, 8388608, 4387857,
      8393728, 8192, 16384, 32768, 8516640, 131088, 304000, 573760, 1073856, 2146624, 8525841,
      1024]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 106 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint106Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint106Transport v =
      monsterCo1GeometryVectorPoint106Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint56Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8445969, 4230159, 15739902, 14698990, 16, 8446000, 192, 64, 24784, 41072, 8445952,
    12583424, 61968, 8413696, 49648, 41952, 5504068, 131270, 2671771, 1859782, 3187963,
    1073174, 4387017, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint56InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 7495579, 5414615, 6438237, 16, 1072, 128, 192, 17296, 49472, 8446992, 12767234,
    13632, 58336, 58032, 58688, 3363653, 2277644, 3982780, 1361388, 49164, 8405003, 10576,
    57360] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint58Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447120, 29824, 29664, 53712, 8389648, 58416, 58560, 58432, 34000, 17520, 8445952,
    12910604, 5245503, 9479681, 2122080, 3195728, 12789860, 9573574, 14183621, 8136760,
    8390379, 3154470, 5692135, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint106AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 4233231, 7355646, 6315246, 16, 58416, 192, 64, 24784, 41072, 58368, 12583438,
    8451600, 8413696, 49648, 41952, 13888116, 131286, 11060635, 1860294, 11577339, 1073686,
    4388055, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint106AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8442194, 8434580, 8418008, 16, 8389664, 64, 128, 256, 512, 8388608, 4387857,
    8393728, 8192, 16384, 32768, 8516640, 131088, 304000, 573760, 1073856, 2146624, 8525841,
    1024] := by rfl
  have hc : monsterCo1GeometryVectorPoint106Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388785, 4242575, 15743102, 14702702, 8389648, 48, 58560, 58432, 34000, 17520, 8389632,
    9748655, 5303871, 9479681, 2122080, 3195728, 1255002, 1183958, 7875956, 7137816, 3179898,
    2154502, 8911477, 8445952] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint56Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint106AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8445969, 4230159, 15739902, 14698990, 16, 8446000, 192, 64, 24784, 41072, 8445952,
    12583424, 61968, 8413696, 49648, 41952, 5504068, 131270, 2671771, 1859782, 3187963,
    1073174, 4387017, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8446993, 4233231, 7355646, 6315246, 16, 58416, 192, 64, 24784, 41072, 58368, 12583438,
    8451600, 8413696, 49648, 41952, 13888116, 131286, 11060635, 1860294, 11577339, 1073686,
    4388055, 8445952] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint106AfterSignMatrix *
    monsterCo1GeometryVectorPoint56InverseMatrix =
    monsterCo1GeometryVectorPoint106AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446993, 4233231, 7355646, 6315246, 16, 58416, 192, 64, 24784, 41072, 58368, 12583438,
    8451600, 8413696, 49648, 41952, 13888116, 131286, 11060635, 1860294, 11577339, 1073686,
    4388055, 8445952]
    ![1041, 7495579, 5414615, 6438237, 16, 1072, 128, 192, 17296, 49472, 8446992, 12767234,
    13632, 58336, 58032, 58688, 3363653, 2277644, 3982780, 1361388, 49164, 8405003, 10576,
    57360]
    ![8446993, 8442194, 8434580, 8418008, 16, 8389664, 64, 128, 256, 512, 8388608, 4387857,
    8393728, 8192, 16384, 32768, 8516640, 131088, 304000, 573760, 1073856, 2146624, 8525841,
    1024] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint106AfterInverseMatrix *
    monsterCo1GeometryVectorPoint58Matrix = monsterCo1GeometryVectorPoint106Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446993, 8442194, 8434580, 8418008, 16, 8389664, 64, 128, 256, 512, 8388608, 4387857,
    8393728, 8192, 16384, 32768, 8516640, 131088, 304000, 573760, 1073856, 2146624, 8525841,
    1024]
    ![8447120, 29824, 29664, 53712, 8389648, 58416, 58560, 58432, 34000, 17520, 8445952,
    12910604, 5245503, 9479681, 2122080, 3195728, 12789860, 9573574, 14183621, 8136760,
    8390379, 3154470, 5692135, 8389632]
    ![8388785, 4242575, 15743102, 14702702, 8389648, 48, 58560, 58432, 34000, 17520, 8389632,
    9748655, 5303871, 9479681, 2122080, 3195728, 1255002, 1183958, 7875956, 7137816, 3179898,
    2154502, 8911477, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint56Transport monsterCo1GeometryVectorPoint58Transport 1
    monsterCo1GeometryVectorPoint56Matrix monsterCo1GeometryVectorPoint56InverseMatrix
    monsterCo1GeometryVectorPoint58Matrix
    monsterCo1GeometryVectorPoint106AfterSignMatrix
    monsterCo1GeometryVectorPoint106AfterInverseMatrix monsterCo1GeometryVectorPoint106Matrix
    monsterCo1GeometryVectorPoint56Transport_binary
    monsterCo1GeometryVectorPoint56Transport_inverse_binary
    monsterCo1GeometryVectorPoint58Transport_binary
    hc1 hc2 hc3 v

/-- Source point 106 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint106 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint106Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint106_binary :
    monsterCo1GeometryVectorPoint106.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint106Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint106Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
