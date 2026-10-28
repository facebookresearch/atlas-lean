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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint039

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 88. -/
def monsterCo1GeometryVectorPoint88Transport : Co1 :=
  monsterCo1GeometryVectorPoint38Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint38Transport⁻¹ * monsterCo1GeometryVectorPoint39Transport

/-- Complete displayed binary matrix of actual transport 88. -/
def monsterCo1GeometryVectorPoint88Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
      8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
      10486012, 8389991, 4522072, 8388848]

/-- First complete finite matrix product in literal actual transport 88. -/
def monsterCo1GeometryVectorPoint88AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447105, 12701184, 15798215, 6416747, 8446000, 8445968, 57568, 8389696, 8422320, 8405392,
      8389632, 5818990, 13761676, 1083373, 10502586, 11584150, 7536611, 13892164, 9991776,
      13499852, 11559532, 8421735, 7677800, 8447008]

/-- Second complete finite matrix product in literal actual transport 88. -/
def monsterCo1GeometryVectorPoint88AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446080, 8674196, 10796738, 9723337, 32, 16, 8446145, 128, 8422871, 17163, 1024, 1373307,
      11832780, 11552736, 1057281, 10520033, 9576576, 8455050, 9749387, 1899643, 3187819,
      2122854, 13681547, 57473]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 88 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint88Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint88Transport v =
      monsterCo1GeometryVectorPoint88Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint38Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint38InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![241, 499185, 10992125, 9943739, 8389648, 48, 1152, 8388800, 8406395, 50460, 8447153,
    8381863, 8401555, 8447809, 57873, 8446433, 3342348, 10621200, 12321192, 1373428, 8439056,
    8406640, 4750547, 8446129] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint88AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447105, 12701184, 15798215, 6416747, 8446000, 8445968, 57568, 8389696, 8422320, 8405392,
    8389632, 5818990, 13761676, 1083373, 10502586, 11584150, 7536611, 13892164, 9991776,
    13499852, 11559532, 8421735, 7677800, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint88AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446080, 8674196, 10796738, 9723337, 32, 16, 8446145, 128, 8422871, 17163, 1024, 1373307,
    11832780, 11552736, 1057281, 10520033, 9576576, 8455050, 9749387, 1899643, 3187819,
    2122854, 13681547, 57473] := by rfl
  have hc : monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint38Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint88AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![8447105, 12701184, 15798215, 6416747, 8446000, 8445968, 57568, 8389696, 8422320, 8405392,
    8389632, 5818990, 13761676, 1083373, 10502586, 11584150, 7536611, 13892164, 9991776,
    13499852, 11559532, 8421735, 7677800, 8447008] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint88AfterSignMatrix *
    monsterCo1GeometryVectorPoint38InverseMatrix =
    monsterCo1GeometryVectorPoint88AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447105, 12701184, 15798215, 6416747, 8446000, 8445968, 57568, 8389696, 8422320, 8405392,
    8389632, 5818990, 13761676, 1083373, 10502586, 11584150, 7536611, 13892164, 9991776,
    13499852, 11559532, 8421735, 7677800, 8447008]
    ![241, 499185, 10992125, 9943739, 8389648, 48, 1152, 8388800, 8406395, 50460, 8447153,
    8381863, 8401555, 8447809, 57873, 8446433, 3342348, 10621200, 12321192, 1373428, 8439056,
    8406640, 4750547, 8446129]
    ![8446080, 8674196, 10796738, 9723337, 32, 16, 8446145, 128, 8422871, 17163, 1024, 1373307,
    11832780, 11552736, 1057281, 10520033, 9576576, 8455050, 9749387, 1899643, 3187819,
    2122854, 13681547, 57473] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint88AfterInverseMatrix *
    monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryVectorPoint88Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446080, 8674196, 10796738, 9723337, 32, 16, 8446145, 128, 8422871, 17163, 1024, 1373307,
    11832780, 11552736, 1057281, 10520033, 9576576, 8455050, 9749387, 1899643, 3187819,
    2122854, 13681547, 57473]
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368]
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint38Transport monsterCo1GeometryVectorPoint39Transport 5
    monsterCo1GeometryVectorPoint38Matrix monsterCo1GeometryVectorPoint38InverseMatrix
    monsterCo1GeometryVectorPoint39Matrix
    monsterCo1GeometryVectorPoint88AfterSignMatrix
    monsterCo1GeometryVectorPoint88AfterInverseMatrix monsterCo1GeometryVectorPoint88Matrix
    monsterCo1GeometryVectorPoint38Transport_binary
    monsterCo1GeometryVectorPoint38Transport_inverse_binary
    monsterCo1GeometryVectorPoint39Transport_binary
    hc1 hc2 hc3 v

/-- Source point 88 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint88 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint88Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint88_binary :
    monsterCo1GeometryVectorPoint88.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint88Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint88Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
