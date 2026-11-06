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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint038

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 85. -/
def monsterCo1GeometryVectorPoint85Transport : Co1 :=
  monsterCo1GeometryVectorPoint35Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint35Transport⁻¹ * monsterCo1GeometryVectorPoint38Transport

/-- Complete displayed binary matrix of actual transport 85. -/
def monsterCo1GeometryVectorPoint85Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58529, 1790917, 10162478, 759097, 8445968, 57424, 8446144, 8389696, 8390352, 42848,
      8389632, 144950, 9167138, 1050214, 9454365, 8430026, 8027952, 13794504, 11072359,
      5021406, 3170570, 33287, 3037368, 1136]

/-- First complete finite matrix product in literal actual transport 85. -/
def monsterCo1GeometryVectorPoint85AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
      5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
      214, 196096, 57360]

/-- Second complete finite matrix product in literal actual transport 85. -/
def monsterCo1GeometryVectorPoint85AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
      10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152,
      14821698, 58385]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 85 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint85Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint85Transport v =
      monsterCo1GeometryVectorPoint85Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint35InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint38Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint85AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360] := by rfl
  have hf : monsterCo1GeometryVectorPoint85AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385] := by rfl
  have hc : monsterCo1GeometryVectorPoint85Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 1790917, 10162478, 759097, 8445968, 57424, 8446144, 8389696, 8390352, 42848,
    8389632, 144950, 9167138, 1050214, 9454365, 8430026, 8027952, 13794504, 11072359, 5021406,
    3170570, 33287, 3037368, 1136] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint35Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint85AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint85AfterSignMatrix *
    monsterCo1GeometryVectorPoint35InverseMatrix =
    monsterCo1GeometryVectorPoint85AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360]
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977]
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint85AfterInverseMatrix *
    monsterCo1GeometryVectorPoint38Matrix = monsterCo1GeometryVectorPoint85Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385]
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368]
    ![58529, 1790917, 10162478, 759097, 8445968, 57424, 8446144, 8389696, 8390352, 42848,
    8389632, 144950, 9167138, 1050214, 9454365, 8430026, 8027952, 13794504, 11072359, 5021406,
    3170570, 33287, 3037368, 1136] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint35Transport monsterCo1GeometryVectorPoint38Transport 6
    monsterCo1GeometryVectorPoint35Matrix monsterCo1GeometryVectorPoint35InverseMatrix
    monsterCo1GeometryVectorPoint38Matrix
    monsterCo1GeometryVectorPoint85AfterSignMatrix
    monsterCo1GeometryVectorPoint85AfterInverseMatrix monsterCo1GeometryVectorPoint85Matrix
    monsterCo1GeometryVectorPoint35Transport_binary
    monsterCo1GeometryVectorPoint35Transport_inverse_binary
    monsterCo1GeometryVectorPoint38Transport_binary
    hc1 hc2 hc3 v

/-- Source point 85 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint85 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint85Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint85_binary :
    monsterCo1GeometryVectorPoint85.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint85Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint85Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
