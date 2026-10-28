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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint042

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 91. -/
def monsterCo1GeometryVectorPoint91Transport : Co1 :=
  monsterCo1GeometryVectorPoint30Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint30Transport⁻¹ * monsterCo1GeometryVectorPoint42Transport

/-- Complete displayed binary matrix of actual transport 91. -/
def monsterCo1GeometryVectorPoint91Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
      8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003,
      11610078, 10560894, 13954732, 8389632]

/-- First complete finite matrix product in literal actual transport 91. -/
def monsterCo1GeometryVectorPoint91AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29040, 57504, 8388640, 32, 57456, 8438384, 49152, 160, 4227792,
      349309, 1074652, 1073777, 1996, 3212163, 15030557, 7035677, 3211824, 11591836, 11591930,
      12334131, 8389632]

/-- Second complete finite matrix product in literal actual transport 91. -/
def monsterCo1GeometryVectorPoint91AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4, 1896, 225, 64, 32, 113, 727, 439, 1120, 3840, 3740454, 3154833, 3163121, 32768,
      3670854, 7176837, 5996820, 3212070, 10518743, 9470135, 12615680, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 91 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint91Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint91Transport v =
      monsterCo1GeometryVectorPoint91Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint30InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96] :=
    by decide +kernel
  have hy : monsterCo1GeometryVectorPoint42Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint91AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29040, 57504, 8388640, 32, 57456, 8438384, 49152, 160, 4227792,
    349309, 1074652, 1073777, 1996, 3212163, 15030557, 7035677, 3211824, 11591836, 11591930,
    12334131, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint91AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4, 1896, 225, 64, 32, 113, 727, 439, 1120, 3840, 3740454, 3154833, 3163121, 32768,
    3670854, 7176837, 5996820, 3212070, 10518743, 9470135, 12615680, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint91Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
    8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003, 11610078,
    10560894, 13954732, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint30Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint91AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8388800, 8451008, 61632, 29040, 57504, 8388640, 32, 57456, 8438384, 49152, 160, 4227792,
    349309, 1074652, 1073777, 1996, 3212163, 15030557, 7035677, 3211824, 11591836, 11591930,
    12334131, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint91AfterSignMatrix *
    monsterCo1GeometryVectorPoint30InverseMatrix =
    monsterCo1GeometryVectorPoint91AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29040, 57504, 8388640, 32, 57456, 8438384, 49152, 160, 4227792,
    349309, 1074652, 1073777, 1996, 3212163, 15030557, 7035677, 3211824, 11591836, 11591930,
    12334131, 8389632]
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96]
    ![1, 2, 4, 1896, 225, 64, 32, 113, 727, 439, 1120, 3840, 3740454, 3154833, 3163121, 32768,
    3670854, 7176837, 5996820, 3212070, 10518743, 9470135, 12615680, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint91AfterInverseMatrix *
    monsterCo1GeometryVectorPoint42Matrix = monsterCo1GeometryVectorPoint91Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 4, 1896, 225, 64, 32, 113, 727, 439, 1120, 3840, 3740454, 3154833, 3163121, 32768,
    3670854, 7176837, 5996820, 3212070, 10518743, 9470135, 12615680, 8388608]
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632]
    ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
    8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003, 11610078,
    10560894, 13954732, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint30Transport monsterCo1GeometryVectorPoint42Transport 6
    monsterCo1GeometryVectorPoint30Matrix monsterCo1GeometryVectorPoint30InverseMatrix
    monsterCo1GeometryVectorPoint42Matrix
    monsterCo1GeometryVectorPoint91AfterSignMatrix
    monsterCo1GeometryVectorPoint91AfterInverseMatrix monsterCo1GeometryVectorPoint91Matrix
    monsterCo1GeometryVectorPoint30Transport_binary
    monsterCo1GeometryVectorPoint30Transport_inverse_binary
    monsterCo1GeometryVectorPoint42Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 91. -/
def monsterCo1GeometryVectorPoint91InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12148838, 12593147, 10970113, 10380289, 841, 97, 8389647, 1, 1510, 912, 1030, 13029360,
      157, 8389526, 8390418, 8390531, 394225, 3278388, 4187024, 11335146, 3146736, 6235485,
      11546471, 8389638]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint91Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint91Transport⁻¹ v =
      monsterCo1GeometryVectorPoint91InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint91Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
        8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003,
        11610078, 10560894, 13954732, 8389632] := by rfl
  have hmi : monsterCo1GeometryVectorPoint91InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![12148838, 12593147, 10970113, 10380289, 841, 97, 8389647, 1, 1510, 912, 1030, 13029360,
        157, 8389526, 8390418, 8390531, 394225, 3278388, 4187024, 11335146, 3146736, 6235485,
        11546471, 8389638] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint91Matrix *
    monsterCo1GeometryVectorPoint91InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
        8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003,
        11610078, 10560894, 13954732, 8389632]
      ![12148838, 12593147, 10970113, 10380289, 841, 97, 8389647, 1, 1510, 912, 1030, 13029360,
        157, 8389526, 8390418, 8390531, 394225, 3278388, 4187024, 11335146, 3146736, 6235485,
        11546471, 8389638]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint91Transport _ _
    monsterCo1GeometryVectorPoint91Transport_binary hc v

/-- Source point 91 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint91 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint91Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint91_binary :
    monsterCo1GeometryVectorPoint91.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint91Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint91Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
