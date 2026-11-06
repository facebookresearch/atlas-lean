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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint063
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint074

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 121. -/
def monsterCo1GeometryVectorPoint121Transport : Co1 :=
  monsterCo1GeometryVectorPoint63Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint63Transport⁻¹ * monsterCo1GeometryVectorPoint74Transport

/-- Complete displayed binary matrix of actual transport 121. -/
def monsterCo1GeometryVectorPoint121Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 15580612, 5069093, 8240430, 8388672, 8445984, 32, 57552, 8414592, 8439056,
      8389632, 6601342, 14502831, 3147754, 1074107, 10518736, 15825107, 12066921, 13523052,
      11617373, 11535575, 8388790, 9288655, 8446176]

/-- First complete finite matrix product in literal actual transport 121. -/
def monsterCo1GeometryVectorPoint121AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 11069661, 10021115, 1609485, 58465, 8447120, 57441, 1, 8438252, 1106955,
      8388768, 1551431, 12413176, 8429786, 11576401, 3203162, 6696039, 634502, 14706536,
      8994111, 11592849, 1936, 265998, 58433]

/-- Second complete finite matrix product in literal actual transport 121. -/
def monsterCo1GeometryVectorPoint121AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 331266, 1378979, 11864671, 58545, 8388656, 58593, 128, 49404, 8423015, 1024, 2265038,
      2481948, 10543372, 11568555, 9471159, 1278857, 3624908, 11829280, 10309436, 8389815,
      10544305, 15018925, 8447137]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 121 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint121Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint121Transport v =
      monsterCo1GeometryVectorPoint121Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint63Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 11135806, 10087262, 10063848, 8447041, 8447152, 8446017, 1, 8438636, 9495719,
    8388768, 1486599, 3959547, 41242, 3188183, 3203132, 15150081, 568399, 14705890, 539830,
    11592951, 8390544, 331021, 8447073] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint63InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 10971647, 3631433, 12052782, 58384, 8388624, 8389649, 57505, 10535181, 8541, 80,
    7863120, 11341109, 10510823, 11560364, 1106987, 156559, 7514569, 1431909, 6460357, 9496070,
    9495041, 10719220, 8447153] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint74Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11986453, 8840755, 11985662, 8446000, 8388736, 57424, 57552, 8390640, 8431040,
    8389632, 10553310, 8811112, 3179868, 8390090, 3179703, 10756562, 7568665, 6216733, 8059371,
    2097328, 8388710, 14058200, 8388752] := by rfl
  have he : monsterCo1GeometryVectorPoint121AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 11069661, 10021115, 1609485, 58465, 8447120, 57441, 1, 8438252, 1106955,
    8388768, 1551431, 12413176, 8429786, 11576401, 3203162, 6696039, 634502, 14706536, 8994111,
    11592849, 1936, 265998, 58433] := by rfl
  have hf : monsterCo1GeometryVectorPoint121AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 331266, 1378979, 11864671, 58545, 8388656, 58593, 128, 49404, 8423015, 1024, 2265038,
    2481948, 10543372, 11568555, 9471159, 1278857, 3624908, 11829280, 10309436, 8389815,
    10544305, 15018925, 8447137] := by rfl
  have hc : monsterCo1GeometryVectorPoint121Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 15580612, 5069093, 8240430, 8388672, 8445984, 32, 57552, 8414592, 8439056,
    8389632, 6601342, 14502831, 3147754, 1074107, 10518736, 15825107, 12066921, 13523052,
    11617373, 11535575, 8388790, 9288655, 8446176] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint63Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint121AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 11135806, 10087262, 10063848, 8447041, 8447152, 8446017, 1, 8438636, 9495719,
    8388768, 1486599, 3959547, 41242, 3188183, 3203132, 15150081, 568399, 14705890, 539830,
    11592951, 8390544, 331021, 8447073]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![8388800, 11069661, 10021115, 1609485, 58465, 8447120, 57441, 1, 8438252, 1106955,
    8388768, 1551431, 12413176, 8429786, 11576401, 3203162, 6696039, 634502, 14706536, 8994111,
    11592849, 1936, 265998, 58433] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint121AfterSignMatrix *
    monsterCo1GeometryVectorPoint63InverseMatrix =
    monsterCo1GeometryVectorPoint121AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 11069661, 10021115, 1609485, 58465, 8447120, 57441, 1, 8438252, 1106955,
    8388768, 1551431, 12413176, 8429786, 11576401, 3203162, 6696039, 634502, 14706536, 8994111,
    11592849, 1936, 265998, 58433]
    ![128, 10971647, 3631433, 12052782, 58384, 8388624, 8389649, 57505, 10535181, 8541, 80,
    7863120, 11341109, 10510823, 11560364, 1106987, 156559, 7514569, 1431909, 6460357, 9496070,
    9495041, 10719220, 8447153]
    ![1, 331266, 1378979, 11864671, 58545, 8388656, 58593, 128, 49404, 8423015, 1024, 2265038,
    2481948, 10543372, 11568555, 9471159, 1278857, 3624908, 11829280, 10309436, 8389815,
    10544305, 15018925, 8447137] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint121AfterInverseMatrix *
    monsterCo1GeometryVectorPoint74Matrix = monsterCo1GeometryVectorPoint121Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 331266, 1378979, 11864671, 58545, 8388656, 58593, 128, 49404, 8423015, 1024, 2265038,
    2481948, 10543372, 11568555, 9471159, 1278857, 3624908, 11829280, 10309436, 8389815,
    10544305, 15018925, 8447137]
    ![8388609, 11986453, 8840755, 11985662, 8446000, 8388736, 57424, 57552, 8390640, 8431040,
    8389632, 10553310, 8811112, 3179868, 8390090, 3179703, 10756562, 7568665, 6216733, 8059371,
    2097328, 8388710, 14058200, 8388752]
    ![8388609, 15580612, 5069093, 8240430, 8388672, 8445984, 32, 57552, 8414592, 8439056,
    8389632, 6601342, 14502831, 3147754, 1074107, 10518736, 15825107, 12066921, 13523052,
    11617373, 11535575, 8388790, 9288655, 8446176] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint63Transport monsterCo1GeometryVectorPoint74Transport 5
    monsterCo1GeometryVectorPoint63Matrix monsterCo1GeometryVectorPoint63InverseMatrix
    monsterCo1GeometryVectorPoint74Matrix
    monsterCo1GeometryVectorPoint121AfterSignMatrix
    monsterCo1GeometryVectorPoint121AfterInverseMatrix monsterCo1GeometryVectorPoint121Matrix
    monsterCo1GeometryVectorPoint63Transport_binary
    monsterCo1GeometryVectorPoint63Transport_inverse_binary
    monsterCo1GeometryVectorPoint74Transport_binary
    hc1 hc2 hc3 v

/-- Source point 121 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint121 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint121Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint121_binary :
    monsterCo1GeometryVectorPoint121.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint121Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint121Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
