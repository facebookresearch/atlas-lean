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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint155

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 164. -/
def monsterCo1GeometryVectorPoint164Transport : Co1 :=
  monsterCo1GeometryVectorPoint40Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint40Transport⁻¹ * monsterCo1GeometryVectorPoint155Transport

/-- Complete displayed binary matrix of actual transport 164. -/
def monsterCo1GeometryVectorPoint164Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 8439328, 7308651, 5501116, 6459196, 14846767, 5393831, 13782312, 14831132,
      6121965, 8605957, 6578947, 6118958, 4904089, 15651222, 6447642, 9558379, 15136261,
      9259191, 29760, 10704147, 14238343, 909537, 4138018]

/-- First complete finite matrix product in literal actual transport 164. -/
def monsterCo1GeometryVectorPoint164AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 3179728, 2131152, 4242511, 4217918, 4226255, 4234270, 4250767, 4209710,
      9438208, 4573357, 10380502, 377516, 13968812, 13969324, 8646666, 8917002, 8581126,
      9179142, 12700706, 12897411, 5627916, 8445952]

/-- Second complete finite matrix product in literal actual transport 164. -/
def monsterCo1GeometryVectorPoint164AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
      2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
      655616, 6957057, 8389644]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 164 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint164Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint164Transport v =
      monsterCo1GeometryVectorPoint164Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint40Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint40InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint164AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 3179728, 2131152, 4242511, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 4573357, 10380502, 377516, 13968812, 13969324, 8646666, 8917002, 8581126, 9179142,
    12700706, 12897411, 5627916, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint164AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint164Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 8439328, 7308651, 5501116, 6459196, 14846767, 5393831, 13782312, 14831132,
    6121965, 8605957, 6578947, 6118958, 4904089, 15651222, 6447642, 9558379, 15136261, 9259191,
    29760, 10704147, 14238343, 909537, 4138018] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint40Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint164AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 3179728, 2131152, 4242511, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 4573357, 10380502, 377516, 13968812, 13969324, 8646666, 8917002, 8581126, 9179142,
    12700706, 12897411, 5627916, 8445952] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint164AfterSignMatrix *
    monsterCo1GeometryVectorPoint40InverseMatrix =
    monsterCo1GeometryVectorPoint164AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 3179728, 2131152, 4242511, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 4573357, 10380502, 377516, 13968812, 13969324, 8646666, 8917002, 8581126, 9179142,
    12700706, 12897411, 5627916, 8445952]
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144]
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint164AfterInverseMatrix *
    monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryVectorPoint164Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644]
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848]
    ![3196566, 8439328, 7308651, 5501116, 6459196, 14846767, 5393831, 13782312, 14831132,
    6121965, 8605957, 6578947, 6118958, 4904089, 15651222, 6447642, 9558379, 15136261, 9259191,
    29760, 10704147, 14238343, 909537, 4138018] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint40Transport monsterCo1GeometryVectorPoint155Transport 1
    monsterCo1GeometryVectorPoint40Matrix monsterCo1GeometryVectorPoint40InverseMatrix
    monsterCo1GeometryVectorPoint155Matrix
    monsterCo1GeometryVectorPoint164AfterSignMatrix
    monsterCo1GeometryVectorPoint164AfterInverseMatrix monsterCo1GeometryVectorPoint164Matrix
    monsterCo1GeometryVectorPoint40Transport_binary
    monsterCo1GeometryVectorPoint40Transport_inverse_binary
    monsterCo1GeometryVectorPoint155Transport_binary
    hc1 hc2 hc3 v

/-- Source point 164 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint164 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint164Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint164_binary :
    monsterCo1GeometryVectorPoint164.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint164Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint164Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
