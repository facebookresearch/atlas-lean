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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint100

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 144. -/
def monsterCo1GeometryVectorPoint144Transport : Co1 :=
  monsterCo1GeometryVectorPoint54Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint54Transport⁻¹ * monsterCo1GeometryVectorPoint100Transport

/-- Complete displayed binary matrix of actual transport 144. -/
def monsterCo1GeometryVectorPoint144Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9365207, 3612400, 15871514, 8760672, 13507402, 816458, 12646749, 9204556, 13541372,
      16512593, 7954877, 11679456, 2137520, 9495844, 7627053, 6972746, 8782451, 1196739,
      1340196, 6331580, 10356111, 12371331, 4605437, 9496263]

/-- First complete finite matrix product in literal actual transport 144. -/
def monsterCo1GeometryVectorPoint144AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58465, 4344784, 8989447, 625335, 6056135, 1785887, 14453767, 10174575, 14479063, 1827807,
      17824, 4941654, 13778758, 1049127, 12565102, 11516072, 5910203, 5118999, 4296303,
      2283068, 8389787, 3162684, 10484930, 1106646]

/-- Second complete finite matrix product in literal actual transport 144. -/
def monsterCo1GeometryVectorPoint144AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11191373, 622774, 2954379, 12073053, 3565618, 5315740, 8996947, 4520001, 2329487,
      13751835, 2754795, 2399291, 16568468, 16082672, 1227465, 15915076, 10987651, 12658690,
      5018638, 5400599, 1048576, 3147782, 10637378, 14647996]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 144 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint144Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint144Transport v =
      monsterCo1GeometryVectorPoint144Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint54Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58481, 12601423, 731995, 756075, 6187208, 10175050, 6196248, 10175034, 6220808, 10215946,
    17968, 4940949, 13647567, 9437921, 12434290, 11385202, 5778990, 13377038, 4426943, 2283296,
    8389787, 3162406, 10354178, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint54InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1197, 11623453, 16465536, 3448012, 11191372, 12566720, 1377324, 12567612, 4132375, 652,
    9773169, 2764079, 8450371, 2811773, 8397425, 4186481, 13390156, 4756190, 258063, 8454467,
    49804, 6966455, 13899249, 1434749] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200] := by rfl
  have he : monsterCo1GeometryVectorPoint144AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 4344784, 8989447, 625335, 6056135, 1785887, 14453767, 10174575, 14479063, 1827807,
    17824, 4941654, 13778758, 1049127, 12565102, 11516072, 5910203, 5118999, 4296303, 2283068,
    8389787, 3162684, 10484930, 1106646] := by rfl
  have hf : monsterCo1GeometryVectorPoint144AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![11191373, 622774, 2954379, 12073053, 3565618, 5315740, 8996947, 4520001, 2329487,
    13751835, 2754795, 2399291, 16568468, 16082672, 1227465, 15915076, 10987651, 12658690,
    5018638, 5400599, 1048576, 3147782, 10637378, 14647996] := by rfl
  have hc : monsterCo1GeometryVectorPoint144Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9365207, 3612400, 15871514, 8760672, 13507402, 816458, 12646749, 9204556, 13541372,
    16512593, 7954877, 11679456, 2137520, 9495844, 7627053, 6972746, 8782451, 1196739, 1340196,
    6331580, 10356111, 12371331, 4605437, 9496263] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint54Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint144AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58481, 12601423, 731995, 756075, 6187208, 10175050, 6196248, 10175034, 6220808, 10215946,
    17968, 4940949, 13647567, 9437921, 12434290, 11385202, 5778990, 13377038, 4426943, 2283296,
    8389787, 3162406, 10354178, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![58465, 4344784, 8989447, 625335, 6056135, 1785887, 14453767, 10174575, 14479063, 1827807,
    17824, 4941654, 13778758, 1049127, 12565102, 11516072, 5910203, 5118999, 4296303, 2283068,
    8389787, 3162684, 10484930, 1106646] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint144AfterSignMatrix *
    monsterCo1GeometryVectorPoint54InverseMatrix =
    monsterCo1GeometryVectorPoint144AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58465, 4344784, 8989447, 625335, 6056135, 1785887, 14453767, 10174575, 14479063, 1827807,
    17824, 4941654, 13778758, 1049127, 12565102, 11516072, 5910203, 5118999, 4296303, 2283068,
    8389787, 3162684, 10484930, 1106646]
    ![1197, 11623453, 16465536, 3448012, 11191372, 12566720, 1377324, 12567612, 4132375, 652,
    9773169, 2764079, 8450371, 2811773, 8397425, 4186481, 13390156, 4756190, 258063, 8454467,
    49804, 6966455, 13899249, 1434749]
    ![11191373, 622774, 2954379, 12073053, 3565618, 5315740, 8996947, 4520001, 2329487,
    13751835, 2754795, 2399291, 16568468, 16082672, 1227465, 15915076, 10987651, 12658690,
    5018638, 5400599, 1048576, 3147782, 10637378, 14647996] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint144AfterInverseMatrix *
    monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryVectorPoint144Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![11191373, 622774, 2954379, 12073053, 3565618, 5315740, 8996947, 4520001, 2329487,
    13751835, 2754795, 2399291, 16568468, 16082672, 1227465, 15915076, 10987651, 12658690,
    5018638, 5400599, 1048576, 3147782, 10637378, 14647996]
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200]
    ![9365207, 3612400, 15871514, 8760672, 13507402, 816458, 12646749, 9204556, 13541372,
    16512593, 7954877, 11679456, 2137520, 9495844, 7627053, 6972746, 8782451, 1196739, 1340196,
    6331580, 10356111, 12371331, 4605437, 9496263] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint54Transport monsterCo1GeometryVectorPoint100Transport 6
    monsterCo1GeometryVectorPoint54Matrix monsterCo1GeometryVectorPoint54InverseMatrix
    monsterCo1GeometryVectorPoint100Matrix
    monsterCo1GeometryVectorPoint144AfterSignMatrix
    monsterCo1GeometryVectorPoint144AfterInverseMatrix monsterCo1GeometryVectorPoint144Matrix
    monsterCo1GeometryVectorPoint54Transport_binary
    monsterCo1GeometryVectorPoint54Transport_inverse_binary
    monsterCo1GeometryVectorPoint100Transport_binary
    hc1 hc2 hc3 v

/-- Source point 144 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint144 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint144Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint144_binary :
    monsterCo1GeometryVectorPoint144.val =
      ![0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint144Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint144Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
