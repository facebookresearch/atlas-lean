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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint088

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 136. -/
def monsterCo1GeometryVectorPoint136Transport : Co1 :=
  monsterCo1GeometryVectorPoint3Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint3Transport⁻¹ * monsterCo1GeometryVectorPoint88Transport

/-- Complete displayed binary matrix of actual transport 136. -/
def monsterCo1GeometryVectorPoint136Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
      8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
      13785811, 5502065, 705793, 6260699, 2276025, 8388848]

/-- First complete finite matrix product in literal actual transport 136. -/
def monsterCo1GeometryVectorPoint136AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 8421728, 8405984, 54192, 13248, 8441984, 12288, 8442528, 12928, 8438400,
      4194304, 11142047, 12517823, 4261892, 4261896, 77952, 8704684, 144271, 8966310, 209484,
      840600, 4261903, 8389632]

/-- Second complete finite matrix product in literal actual transport 136. -/
def monsterCo1GeometryVectorPoint136AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
      1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 136 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint136Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint136Transport v =
      monsterCo1GeometryVectorPoint136Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint3Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 4194304,
    2752604, 4129020, 4196363, 4196359, 78336, 315904, 143616, 577792, 209091, 839730, 4196352,
    8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint3InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 5604000, 5587616, 274, 323, 546, 643, 2, 3, 8389644, 4196352, 268, 780,
    11, 7, 66051, 262658, 131331, 524546, 209088, 839728, 2048, 1036] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint136AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 8421728, 8405984, 54192, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    4194304, 11142047, 12517823, 4261892, 4261896, 77952, 8704684, 144271, 8966310, 209484,
    840600, 4261903, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint136AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint136Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint3Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint136AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 4194304,
    2752604, 4129020, 4196363, 4196359, 78336, 315904, 143616, 577792, 209091, 839730, 4196352,
    8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![768, 256, 8421728, 8405984, 54192, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    4194304, 11142047, 12517823, 4261892, 4261896, 77952, 8704684, 144271, 8966310, 209484,
    840600, 4261903, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint136AfterSignMatrix *
    monsterCo1GeometryVectorPoint3InverseMatrix =
    monsterCo1GeometryVectorPoint136AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 8421728, 8405984, 54192, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    4194304, 11142047, 12517823, 4261892, 4261896, 77952, 8704684, 144271, 8966310, 209484,
    840600, 4261903, 8389632]
    ![4129776, 2752848, 5604000, 5587616, 274, 323, 546, 643, 2, 3, 8389644, 4196352, 268, 780,
    11, 7, 66051, 262658, 131331, 524546, 209088, 839728, 2048, 1036]
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint136AfterInverseMatrix *
    monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryVectorPoint136Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608]
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848]
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint3Transport monsterCo1GeometryVectorPoint88Transport 5
    monsterCo1GeometryVectorPoint3Matrix monsterCo1GeometryVectorPoint3InverseMatrix
    monsterCo1GeometryVectorPoint88Matrix
    monsterCo1GeometryVectorPoint136AfterSignMatrix
    monsterCo1GeometryVectorPoint136AfterInverseMatrix monsterCo1GeometryVectorPoint136Matrix
    monsterCo1GeometryVectorPoint3Transport_binary
    monsterCo1GeometryVectorPoint3Transport_inverse_binary
    monsterCo1GeometryVectorPoint88Transport_binary
    hc1 hc2 hc3 v

/-- Source point 136 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint136 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint136Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint136_binary :
    monsterCo1GeometryVectorPoint136.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint136Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint136Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
