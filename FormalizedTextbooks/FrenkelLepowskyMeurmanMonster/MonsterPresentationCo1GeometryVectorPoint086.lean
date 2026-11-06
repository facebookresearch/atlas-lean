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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint039

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 86. -/
def monsterCo1GeometryVectorPoint86Transport : Co1 :=
  monsterCo1GeometryVectorPoint8Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint8Transport⁻¹ * monsterCo1GeometryVectorPoint39Transport

/-- Complete displayed binary matrix of actual transport 86. -/
def monsterCo1GeometryVectorPoint86Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388624, 36864, 8401904, 8409568, 16, 58416, 192, 64, 24784, 41072, 58368, 12583439,
      13637663, 9470977, 10494192, 11550944, 13831748, 131270, 11060699, 1860102, 11536267,
      1049286, 8581833, 8389632]

/-- First complete finite matrix product in literal actual transport 86. -/
def monsterCo1GeometryVectorPoint86AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58369, 12585999, 7342862, 6293774, 58384, 58416, 58560, 58432, 34000, 17520, 8445952,
      343171, 8442496, 8447648, 49568, 50080, 12807268, 12758248, 13142261, 13387865, 9495259,
      9495159, 12592814, 58368]

/-- Second complete finite matrix product in literal actual transport 86. -/
def monsterCo1GeometryVectorPoint86AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58609, 54066, 8433860, 8417480, 8389648, 8389664, 8389696, 8389760, 8389888, 8390144,
      8388608, 8372418, 4096, 8397824, 16384, 32768, 78816, 144336, 8705840, 8967984, 1058032,
      2106608, 4135874, 1024]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 86 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint86Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint86Transport v =
      monsterCo1GeometryVectorPoint86Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint8Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 4201487, 7346190, 6297614, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    58368, 338093, 8442496, 58016, 49568, 50080, 12811348, 12762360, 13147381, 13392985,
    9495771, 9495671, 4203168, 8445952] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint8InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57585, 13573938, 7281567, 6232943, 8388624, 48, 8388736, 192, 17152, 49152, 58608,
    4131825, 8401856, 58112, 8446544, 8446368, 3343344, 10618478, 3933168, 9700719, 12, 1035,
    4203504, 8446192] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint86AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58369, 12585999, 7342862, 6293774, 58384, 58416, 58560, 58432, 34000, 17520, 8445952,
    343171, 8442496, 8447648, 49568, 50080, 12807268, 12758248, 13142261, 13387865, 9495259,
    9495159, 12592814, 58368] := by rfl
  have hf : monsterCo1GeometryVectorPoint86AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58609, 54066, 8433860, 8417480, 8389648, 8389664, 8389696, 8389760, 8389888, 8390144,
    8388608, 8372418, 4096, 8397824, 16384, 32768, 78816, 144336, 8705840, 8967984, 1058032,
    2106608, 4135874, 1024] := by rfl
  have hc : monsterCo1GeometryVectorPoint86Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388624, 36864, 8401904, 8409568, 16, 58416, 192, 64, 24784, 41072, 58368, 12583439,
    13637663, 9470977, 10494192, 11550944, 13831748, 131270, 11060699, 1860102, 11536267,
    1049286, 8581833, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint8Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint86AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57345, 4201487, 7346190, 6297614, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    58368, 338093, 8442496, 58016, 49568, 50080, 12811348, 12762360, 13147381, 13392985,
    9495771, 9495671, 4203168, 8445952]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![58369, 12585999, 7342862, 6293774, 58384, 58416, 58560, 58432, 34000, 17520, 8445952,
    343171, 8442496, 8447648, 49568, 50080, 12807268, 12758248, 13142261, 13387865, 9495259,
    9495159, 12592814, 58368] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint86AfterSignMatrix *
    monsterCo1GeometryVectorPoint8InverseMatrix =
    monsterCo1GeometryVectorPoint86AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58369, 12585999, 7342862, 6293774, 58384, 58416, 58560, 58432, 34000, 17520, 8445952,
    343171, 8442496, 8447648, 49568, 50080, 12807268, 12758248, 13142261, 13387865, 9495259,
    9495159, 12592814, 58368]
    ![57585, 13573938, 7281567, 6232943, 8388624, 48, 8388736, 192, 17152, 49152, 58608,
    4131825, 8401856, 58112, 8446544, 8446368, 3343344, 10618478, 3933168, 9700719, 12, 1035,
    4203504, 8446192]
    ![58609, 54066, 8433860, 8417480, 8389648, 8389664, 8389696, 8389760, 8389888, 8390144,
    8388608, 8372418, 4096, 8397824, 16384, 32768, 78816, 144336, 8705840, 8967984, 1058032,
    2106608, 4135874, 1024] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint86AfterInverseMatrix *
    monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryVectorPoint86Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58609, 54066, 8433860, 8417480, 8389648, 8389664, 8389696, 8389760, 8389888, 8390144,
    8388608, 8372418, 4096, 8397824, 16384, 32768, 78816, 144336, 8705840, 8967984, 1058032,
    2106608, 4135874, 1024]
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368]
    ![8388624, 36864, 8401904, 8409568, 16, 58416, 192, 64, 24784, 41072, 58368, 12583439,
    13637663, 9470977, 10494192, 11550944, 13831748, 131270, 11060699, 1860102, 11536267,
    1049286, 8581833, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint8Transport monsterCo1GeometryVectorPoint39Transport 1
    monsterCo1GeometryVectorPoint8Matrix monsterCo1GeometryVectorPoint8InverseMatrix
    monsterCo1GeometryVectorPoint39Matrix
    monsterCo1GeometryVectorPoint86AfterSignMatrix
    monsterCo1GeometryVectorPoint86AfterInverseMatrix monsterCo1GeometryVectorPoint86Matrix
    monsterCo1GeometryVectorPoint8Transport_binary
    monsterCo1GeometryVectorPoint8Transport_inverse_binary
    monsterCo1GeometryVectorPoint39Transport_binary
    hc1 hc2 hc3 v

/-- Source point 86 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint86 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint86Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint86_binary :
    monsterCo1GeometryVectorPoint86.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint86Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint86Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
