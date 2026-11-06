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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint160

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 168. -/
def monsterCo1GeometryVectorPoint168Transport : Co1 :=
  monsterCo1GeometryVectorPoint91Transport * monsterCo1GeometryTransportOperator 7 *
    monsterCo1GeometryVectorPoint91Transport⁻¹ * monsterCo1GeometryVectorPoint160Transport

/-- Complete displayed binary matrix of actual transport 168. -/
def monsterCo1GeometryVectorPoint168Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 992408, 8439056, 1888, 48, 9372360, 9968, 4138163, 11536155, 1197, 9429545,
      7576876, 14684628, 10686747, 15696037, 10005458, 4874470, 16018011, 16468592, 15149499,
      15207187, 17296, 6332420, 8388848]

/-- First complete finite matrix product in literal actual transport 168. -/
def monsterCo1GeometryVectorPoint168AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 63040, 53984, 192, 20944, 49232, 49392, 37744, 38608, 22128, 8352, 64512, 9430929,
      13647372, 5250561, 8725037, 10494433, 1193014, 1258522, 11543393, 11609960, 10560996,
      5303822, 8389632]

/-- Second complete finite matrix product in literal actual transport 168. -/
def monsterCo1GeometryVectorPoint168AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 3, 8390643, 8389646, 1326, 8390615, 8390583, 1615, 1999, 1854, 8389622, 4638828,
      1996256, 8381436, 16745482, 12158054, 6701858, 15024667, 14303627, 5653315, 7815379,
      8274098, 4177933, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 168 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint168Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint168Transport v =
      monsterCo1GeometryVectorPoint168Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint91Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
    8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003, 11610078,
    10560894, 13954732, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint91InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12148838, 12593147, 10970113, 10380289, 841, 97, 8389647, 1, 1510, 912, 1030, 13029360,
    157, 8389526, 8390418, 8390531, 394225, 3278388, 4187024, 11335146, 3146736, 6235485,
    11546471, 8389638] := by rfl
  have hy : monsterCo1GeometryVectorPoint160Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint168AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63040, 53984, 192, 20944, 49232, 49392, 37744, 38608, 22128, 8352, 64512, 9430929,
    13647372, 5250561, 8725037, 10494433, 1193014, 1258522, 11543393, 11609960, 10560996,
    5303822, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint168AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 3, 8390643, 8389646, 1326, 8390615, 8390583, 1615, 1999, 1854, 8389622, 4638828,
    1996256, 8381436, 16745482, 12158054, 6701858, 15024667, 14303627, 5653315, 7815379,
    8274098, 4177933, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint168Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 992408, 8439056, 1888, 48, 9372360, 9968, 4138163, 11536155, 1197, 9429545,
    7576876, 14684628, 10686747, 15696037, 10005458, 4874470, 16018011, 16468592, 15149499,
    15207187, 17296, 6332420, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint91Matrix *
    monsterCo1GeometryTransportOperatorMatrix 7 =
    monsterCo1GeometryVectorPoint168AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 8442048, 8388800, 21056, 8438384, 8438480, 37568, 38752, 21984, 8397312,
    8715406, 1041945, 5520526, 5512739, 336513, 10494839, 9582000, 9648016, 11543003, 11610078,
    10560894, 13954732, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 7)
    ![128, 63040, 53984, 192, 20944, 49232, 49392, 37744, 38608, 22128, 8352, 64512, 9430929,
    13647372, 5250561, 8725037, 10494433, 1193014, 1258522, 11543393, 11609960, 10560996,
    5303822, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 7) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint168AfterSignMatrix *
    monsterCo1GeometryVectorPoint91InverseMatrix =
    monsterCo1GeometryVectorPoint168AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63040, 53984, 192, 20944, 49232, 49392, 37744, 38608, 22128, 8352, 64512, 9430929,
    13647372, 5250561, 8725037, 10494433, 1193014, 1258522, 11543393, 11609960, 10560996,
    5303822, 8389632]
    ![12148838, 12593147, 10970113, 10380289, 841, 97, 8389647, 1, 1510, 912, 1030, 13029360,
    157, 8389526, 8390418, 8390531, 394225, 3278388, 4187024, 11335146, 3146736, 6235485,
    11546471, 8389638]
    ![1, 3, 8390643, 8389646, 1326, 8390615, 8390583, 1615, 1999, 1854, 8389622, 4638828,
    1996256, 8381436, 16745482, 12158054, 6701858, 15024667, 14303627, 5653315, 7815379,
    8274098, 4177933, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint168AfterInverseMatrix *
    monsterCo1GeometryVectorPoint160Matrix = monsterCo1GeometryVectorPoint168Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 3, 8390643, 8389646, 1326, 8390615, 8390583, 1615, 1999, 1854, 8389622, 4638828,
    1996256, 8381436, 16745482, 12158054, 6701858, 15024667, 14303627, 5653315, 7815379,
    8274098, 4177933, 8388608]
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848]
    ![9380969, 992408, 8439056, 1888, 48, 9372360, 9968, 4138163, 11536155, 1197, 9429545,
    7576876, 14684628, 10686747, 15696037, 10005458, 4874470, 16018011, 16468592, 15149499,
    15207187, 17296, 6332420, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint91Transport monsterCo1GeometryVectorPoint160Transport 7
    monsterCo1GeometryVectorPoint91Matrix monsterCo1GeometryVectorPoint91InverseMatrix
    monsterCo1GeometryVectorPoint160Matrix
    monsterCo1GeometryVectorPoint168AfterSignMatrix
    monsterCo1GeometryVectorPoint168AfterInverseMatrix monsterCo1GeometryVectorPoint168Matrix
    monsterCo1GeometryVectorPoint91Transport_binary
    monsterCo1GeometryVectorPoint91Transport_inverse_binary
    monsterCo1GeometryVectorPoint160Transport_binary
    hc1 hc2 hc3 v

/-- Source point 168 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint168 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint168Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint168_binary :
    monsterCo1GeometryVectorPoint168.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint168Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint168Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
