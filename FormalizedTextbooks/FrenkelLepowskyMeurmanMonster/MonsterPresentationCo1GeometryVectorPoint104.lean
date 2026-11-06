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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint041
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 104. -/
def monsterCo1GeometryVectorPoint104Transport : Co1 :=
  monsterCo1GeometryVectorPoint41Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint41Transport⁻¹ * monsterCo1GeometryVectorPoint57Transport

/-- Complete displayed binary matrix of actual transport 104. -/
def monsterCo1GeometryVectorPoint104Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![6444606, 8421728, 3342624, 2138400, 11218082, 2914918, 13204297, 13510809, 11336161,
      11250245, 9762183, 15203769, 8401731, 16650644, 15569070, 16659657, 8680462, 6943622,
      446976, 452035, 7271811, 266792, 5091822, 481248]

/-- First complete finite matrix product in literal actual transport 104. -/
def monsterCo1GeometryVectorPoint104AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 8414736, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
      12724593, 1106646, 9961455, 2023622, 9765871, 15067003, 16115645, 12655652, 13245718,
      4201479, 13508112, 79171, 316118, 4531927, 8446992]

/-- Second complete finite matrix product in literal actual transport 104. -/
def monsterCo1GeometryVectorPoint104AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![16729717, 8439328, 8598633, 3155275, 548437, 8936315, 4724865, 7806383, 8952167, 565113,
      9179328, 5406407, 12571596, 10127396, 10033771, 2804549, 2299136, 3832582, 15981325,
      13372417, 3836025, 10695789, 11139728, 12518894]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 104 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint104Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint104Transport v =
      monsterCo1GeometryVectorPoint104Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint41Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9495040, 1440803, 10412566, 1376300, 15066146, 16114722, 12786740, 4725765,
    12721176, 4987913, 78860, 8704140, 12919938, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint41InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 15019277, 14039565, 14277133, 8389918, 81, 8390287, 161, 12599307, 49164,
    4130044, 8382045, 9765024, 12518413, 4129587, 4129730, 712785, 10620958, 385024, 1373696,
    49152, 4210689, 9776636, 12517616] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint104AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 8414736, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 1106646, 9961455, 2023622, 9765871, 15067003, 16115645, 12655652, 13245718,
    4201479, 13508112, 79171, 316118, 4531927, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint104AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![16729717, 8439328, 8598633, 3155275, 548437, 8936315, 4724865, 7806383, 8952167, 565113,
    9179328, 5406407, 12571596, 10127396, 10033771, 2804549, 2299136, 3832582, 15981325,
    13372417, 3836025, 10695789, 11139728, 12518894] := by rfl
  have hc : monsterCo1GeometryVectorPoint104Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![6444606, 8421728, 3342624, 2138400, 11218082, 2914918, 13204297, 13510809, 11336161,
    11250245, 9762183, 15203769, 8401731, 16650644, 15569070, 16659657, 8680462, 6943622,
    446976, 452035, 7271811, 266792, 5091822, 481248] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint41Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint104AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8414416, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9495040, 1440803, 10412566, 1376300, 15066146, 16114722, 12786740, 4725765,
    12721176, 4987913, 78860, 8704140, 12919938, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 8414736, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 1106646, 9961455, 2023622, 9765871, 15067003, 16115645, 12655652, 13245718,
    4201479, 13508112, 79171, 316118, 4531927, 8446992] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint104AfterSignMatrix *
    monsterCo1GeometryVectorPoint41InverseMatrix =
    monsterCo1GeometryVectorPoint104AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 8414736, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 1106646, 9961455, 2023622, 9765871, 15067003, 16115645, 12655652, 13245718,
    4201479, 13508112, 79171, 316118, 4531927, 8446992]
    ![8389616, 15019277, 14039565, 14277133, 8389918, 81, 8390287, 161, 12599307, 49164,
    4130044, 8382045, 9765024, 12518413, 4129587, 4129730, 712785, 10620958, 385024, 1373696,
    49152, 4210689, 9776636, 12517616]
    ![16729717, 8439328, 8598633, 3155275, 548437, 8936315, 4724865, 7806383, 8952167, 565113,
    9179328, 5406407, 12571596, 10127396, 10033771, 2804549, 2299136, 3832582, 15981325,
    13372417, 3836025, 10695789, 11139728, 12518894] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint104AfterInverseMatrix *
    monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryVectorPoint104Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![16729717, 8439328, 8598633, 3155275, 548437, 8936315, 4724865, 7806383, 8952167, 565113,
    9179328, 5406407, 12571596, 10127396, 10033771, 2804549, 2299136, 3832582, 15981325,
    13372417, 3836025, 10695789, 11139728, 12518894]
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
    ![6444606, 8421728, 3342624, 2138400, 11218082, 2914918, 13204297, 13510809, 11336161,
    11250245, 9762183, 15203769, 8401731, 16650644, 15569070, 16659657, 8680462, 6943622,
    446976, 452035, 7271811, 266792, 5091822, 481248] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint41Transport monsterCo1GeometryVectorPoint57Transport 6
    monsterCo1GeometryVectorPoint41Matrix monsterCo1GeometryVectorPoint41InverseMatrix
    monsterCo1GeometryVectorPoint57Matrix
    monsterCo1GeometryVectorPoint104AfterSignMatrix
    monsterCo1GeometryVectorPoint104AfterInverseMatrix monsterCo1GeometryVectorPoint104Matrix
    monsterCo1GeometryVectorPoint41Transport_binary
    monsterCo1GeometryVectorPoint41Transport_inverse_binary
    monsterCo1GeometryVectorPoint57Transport_binary
    hc1 hc2 hc3 v

/-- Source point 104 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint104 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint104Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint104_binary :
    monsterCo1GeometryVectorPoint104.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint104Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint104Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
