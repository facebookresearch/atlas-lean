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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint088

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 138. -/
def monsterCo1GeometryVectorPoint138Transport : Co1 :=
  monsterCo1GeometryVectorPoint34Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint34Transport⁻¹ * monsterCo1GeometryVectorPoint88Transport

/-- Complete displayed binary matrix of actual transport 138. -/
def monsterCo1GeometryVectorPoint138Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11191564, 1385571, 15231224, 6859028, 4142079, 8397216, 4142771, 8397296, 4141443,
      8446016, 8439216, 14634013, 12530002, 49181, 3162582, 3179994, 15892019, 3379591,
      5397135, 5973671, 9094493, 5735889, 4522072, 8438080]

/-- First complete finite matrix product in literal actual transport 138. -/
def monsterCo1GeometryVectorPoint138AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5557416, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
      8438400, 8473060, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262,
      8597564, 840312, 4194315, 50816]

/-- Second complete finite matrix product in literal actual transport 138. -/
def monsterCo1GeometryVectorPoint138AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
      1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876,
      6268987, 4194304, 8389248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 138 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint138Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint138Transport v =
      monsterCo1GeometryVectorPoint138Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint34Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5622951, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8437760,
    18443, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 209587, 840146,
    4194315, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint34InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 13978279, 5589675, 53520, 12608, 53792, 12928, 53248, 12288, 50176,
    4194315, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 197299, 786898,
    18443, 8437760] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint138AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5557416, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 8473060, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262,
    8597564, 840312, 4194315, 50816] := by rfl
  have hf : monsterCo1GeometryVectorPoint138AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248] := by rfl
  have hc : monsterCo1GeometryVectorPoint138Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11191564, 1385571, 15231224, 6859028, 4142079, 8397216, 4142771, 8397296, 4141443,
    8446016, 8439216, 14634013, 12530002, 49181, 3162582, 3179994, 15892019, 3379591, 5397135,
    5973671, 9094493, 5735889, 4522072, 8438080] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint34Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint138AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5622951, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8437760,
    18443, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 209587, 840146,
    4194315, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12517811, 11142035, 5557416, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 8473060, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262,
    8597564, 840312, 4194315, 50816] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint138AfterSignMatrix *
    monsterCo1GeometryVectorPoint34InverseMatrix =
    monsterCo1GeometryVectorPoint138AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12517811, 11142035, 5557416, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 8473060, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262,
    8597564, 840312, 4194315, 50816]
    ![4129776, 2752848, 13978279, 5589675, 53520, 12608, 53792, 12928, 53248, 12288, 50176,
    4194315, 8439040, 8439552, 16384, 8422400, 78816, 315792, 144016, 578416, 197299, 786898,
    18443, 8437760]
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint138AfterInverseMatrix *
    monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryVectorPoint138Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248]
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848]
    ![11191564, 1385571, 15231224, 6859028, 4142079, 8397216, 4142771, 8397296, 4141443,
    8446016, 8439216, 14634013, 12530002, 49181, 3162582, 3179994, 15892019, 3379591, 5397135,
    5973671, 9094493, 5735889, 4522072, 8438080] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint34Transport monsterCo1GeometryVectorPoint88Transport 5
    monsterCo1GeometryVectorPoint34Matrix monsterCo1GeometryVectorPoint34InverseMatrix
    monsterCo1GeometryVectorPoint88Matrix
    monsterCo1GeometryVectorPoint138AfterSignMatrix
    monsterCo1GeometryVectorPoint138AfterInverseMatrix monsterCo1GeometryVectorPoint138Matrix
    monsterCo1GeometryVectorPoint34Transport_binary
    monsterCo1GeometryVectorPoint34Transport_inverse_binary
    monsterCo1GeometryVectorPoint88Transport_binary
    hc1 hc2 hc3 v

/-- Source point 138 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint138 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint138Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint138_binary :
    monsterCo1GeometryVectorPoint138.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint138Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint138Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
