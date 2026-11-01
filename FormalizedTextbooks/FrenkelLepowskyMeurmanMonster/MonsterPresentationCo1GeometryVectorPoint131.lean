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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint083

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 131. -/
def monsterCo1GeometryVectorPoint131Transport : Co1 :=
  monsterCo1GeometryVectorPoint53Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint53Transport⁻¹ * monsterCo1GeometryVectorPoint83Transport

/-- Complete displayed binary matrix of actual transport 131. -/
def monsterCo1GeometryVectorPoint131Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![943172, 10714247, 9031814, 8442530, 9331860, 8847489, 9331955, 917925, 483504, 11193223,
      484711, 8389390, 7566026, 7800064, 666471, 7614277, 9948716, 1197814, 14077728, 14820563,
      13172776, 16343588, 2670537, 8422663]

/-- First complete finite matrix product in literal actual transport 131. -/
def monsterCo1GeometryVectorPoint131AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![365049, 5024558, 677541, 9102885, 366505, 8737849, 365913, 8766649, 337444, 13011254,
      8718217, 9819568, 11718491, 10749769, 7527284, 14044877, 9133203, 6866822, 15664613,
      5002139, 2168064, 2209296, 9804475, 10224]

/-- Second complete finite matrix product in literal actual transport 131. -/
def monsterCo1GeometryVectorPoint131AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![5399298, 3267863, 504086, 7890381, 5399315, 2970596, 7489374, 13796377, 2995924, 1486346,
      9278531, 4718931, 13216602, 15038749, 1502218, 2917975, 10316107, 131072, 14058649,
      1216064, 8911379, 3612041, 8170188, 2107287]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 131 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint131Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint131Transport v =
      monsterCo1GeometryVectorPoint131Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint53Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint53InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
    2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
    7220845, 8423264, 9022717, 14666619, 2106397] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint83Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8417472, 8435536, 53648, 16, 48, 192, 58432, 24784, 41072, 58368, 6349582,
    13696015, 1074177, 10502288, 3194960, 11748283, 1197814, 14166725, 827526, 10487243,
    1107622, 9221000, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint131AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![365049, 5024558, 677541, 9102885, 366505, 8737849, 365913, 8766649, 337444, 13011254,
    8718217, 9819568, 11718491, 10749769, 7527284, 14044877, 9133203, 6866822, 15664613,
    5002139, 2168064, 2209296, 9804475, 10224] := by rfl
  have hf : monsterCo1GeometryVectorPoint131AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![5399298, 3267863, 504086, 7890381, 5399315, 2970596, 7489374, 13796377, 2995924, 1486346,
    9278531, 4718931, 13216602, 15038749, 1502218, 2917975, 10316107, 131072, 14058649,
    1216064, 8911379, 3612041, 8170188, 2107287] := by rfl
  have hc : monsterCo1GeometryVectorPoint131Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![943172, 10714247, 9031814, 8442530, 9331860, 8847489, 9331955, 917925, 483504, 11193223,
    484711, 8389390, 7566026, 7800064, 666471, 7614277, 9948716, 1197814, 14077728, 14820563,
    13172776, 16343588, 2670537, 8422663] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint53Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint131AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![365049, 5024558, 677541, 9102885, 366505, 8737849, 365913, 8766649, 337444, 13011254,
    8718217, 9819568, 11718491, 10749769, 7527284, 14044877, 9133203, 6866822, 15664613,
    5002139, 2168064, 2209296, 9804475, 10224] hx (monsterCo1GeometryBinaryOperatorMasks_decode
    6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint131AfterSignMatrix *
    monsterCo1GeometryVectorPoint53InverseMatrix =
    monsterCo1GeometryVectorPoint131AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![365049, 5024558, 677541, 9102885, 366505, 8737849, 365913, 8766649, 337444, 13011254,
    8718217, 9819568, 11718491, 10749769, 7527284, 14044877, 9133203, 6866822, 15664613,
    5002139, 2168064, 2209296, 9804475, 10224]
    ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
    2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
    7220845, 8423264, 9022717, 14666619, 2106397]
    ![5399298, 3267863, 504086, 7890381, 5399315, 2970596, 7489374, 13796377, 2995924, 1486346,
    9278531, 4718931, 13216602, 15038749, 1502218, 2917975, 10316107, 131072, 14058649,
    1216064, 8911379, 3612041, 8170188, 2107287] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint131AfterInverseMatrix *
    monsterCo1GeometryVectorPoint83Matrix = monsterCo1GeometryVectorPoint131Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![5399298, 3267863, 504086, 7890381, 5399315, 2970596, 7489374, 13796377, 2995924, 1486346,
    9278531, 4718931, 13216602, 15038749, 1502218, 2917975, 10316107, 131072, 14058649,
    1216064, 8911379, 3612041, 8170188, 2107287]
    ![8388800, 8417472, 8435536, 53648, 16, 48, 192, 58432, 24784, 41072, 58368, 6349582,
    13696015, 1074177, 10502288, 3194960, 11748283, 1197814, 14166725, 827526, 10487243,
    1107622, 9221000, 8389632]
    ![943172, 10714247, 9031814, 8442530, 9331860, 8847489, 9331955, 917925, 483504, 11193223,
    484711, 8389390, 7566026, 7800064, 666471, 7614277, 9948716, 1197814, 14077728, 14820563,
    13172776, 16343588, 2670537, 8422663] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint53Transport monsterCo1GeometryVectorPoint83Transport 6
    monsterCo1GeometryVectorPoint53Matrix monsterCo1GeometryVectorPoint53InverseMatrix
    monsterCo1GeometryVectorPoint83Matrix
    monsterCo1GeometryVectorPoint131AfterSignMatrix
    monsterCo1GeometryVectorPoint131AfterInverseMatrix monsterCo1GeometryVectorPoint131Matrix
    monsterCo1GeometryVectorPoint53Transport_binary
    monsterCo1GeometryVectorPoint53Transport_inverse_binary
    monsterCo1GeometryVectorPoint83Transport_binary
    hc1 hc2 hc3 v

/-- Source point 131 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint131 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint131Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint131_binary :
    monsterCo1GeometryVectorPoint131.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint131Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint131Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
