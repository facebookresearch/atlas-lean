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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 105. -/
def monsterCo1GeometryVectorPoint105Transport : Co1 :=
  monsterCo1GeometryVectorPoint55Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint55Transport⁻¹ * monsterCo1GeometryVectorPoint57Transport

/-- Complete displayed binary matrix of actual transport 105. -/
def monsterCo1GeometryVectorPoint105Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1041, 11007417, 512659, 11007854, 8388736, 58400, 8447088, 1072, 26608, 25104, 8388784,
      9132595, 13824, 8430496, 25696, 8976, 5352069, 11797829, 9671444, 16493831, 9495719,
      3155953, 6628280, 1200]

/-- First complete finite matrix product in literal actual transport 105. -/
def monsterCo1GeometryVectorPoint105AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1152, 8434688, 8434144, 61952, 57552, 32, 1056, 8446016, 8423264, 8421376, 96, 69391,
      12128391, 11543297, 11551175, 8421895, 66400, 15662429, 15267934, 78819, 2148343,
      2123485, 9700515, 8389632]

/-- Second complete finite matrix product in literal actual transport 105. -/
def monsterCo1GeometryVectorPoint105AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388612, 8388610, 8, 48, 32, 64, 8388800, 8389120, 8388864, 1024, 3697519, 8393472,
      8406752, 8398240, 8422144, 65536, 8586054, 9175586, 525062, 10486957, 9438443, 4195078,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 105 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint105Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint105Transport v =
      monsterCo1GeometryVectorPoint105Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint55Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1152, 46560, 45056, 61952, 57584, 32, 1056, 57440, 33792, 33632, 96, 3840, 3740647,
    3154407, 3162209, 33127, 66400, 7339165, 6945693, 78179, 10536381, 10511703, 9700899,
    8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint55InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57569, 647906, 623460, 3793256, 241, 32, 1056, 97, 1031, 871, 96, 3840, 2031, 1675, 875,
    352, 66400, 7284127, 6890143, 78179, 10494939, 10519633, 9715488, 8388704] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint105AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1152, 8434688, 8434144, 61952, 57552, 32, 1056, 8446016, 8423264, 8421376, 96, 69391,
    12128391, 11543297, 11551175, 8421895, 66400, 15662429, 15267934, 78819, 2148343, 2123485,
    9700515, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint105AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388612, 8388610, 8, 48, 32, 64, 8388800, 8389120, 8388864, 1024, 3697519, 8393472,
    8406752, 8398240, 8422144, 65536, 8586054, 9175586, 525062, 10486957, 9438443, 4195078,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint105Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 11007417, 512659, 11007854, 8388736, 58400, 8447088, 1072, 26608, 25104, 8388784,
    9132595, 13824, 8430496, 25696, 8976, 5352069, 11797829, 9671444, 16493831, 9495719,
    3155953, 6628280, 1200] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint55Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint105AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1152, 46560, 45056, 61952, 57584, 32, 1056, 57440, 33792, 33632, 96, 3840, 3740647,
    3154407, 3162209, 33127, 66400, 7339165, 6945693, 78179, 10536381, 10511703, 9700899,
    8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![1152, 8434688, 8434144, 61952, 57552, 32, 1056, 8446016, 8423264, 8421376, 96, 69391,
    12128391, 11543297, 11551175, 8421895, 66400, 15662429, 15267934, 78819, 2148343, 2123485,
    9700515, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint105AfterSignMatrix *
    monsterCo1GeometryVectorPoint55InverseMatrix =
    monsterCo1GeometryVectorPoint105AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1152, 8434688, 8434144, 61952, 57552, 32, 1056, 8446016, 8423264, 8421376, 96, 69391,
    12128391, 11543297, 11551175, 8421895, 66400, 15662429, 15267934, 78819, 2148343, 2123485,
    9700515, 8389632]
    ![57569, 647906, 623460, 3793256, 241, 32, 1056, 97, 1031, 871, 96, 3840, 2031, 1675, 875,
    352, 66400, 7284127, 6890143, 78179, 10494939, 10519633, 9715488, 8388704]
    ![1, 8388612, 8388610, 8, 48, 32, 64, 8388800, 8389120, 8388864, 1024, 3697519, 8393472,
    8406752, 8398240, 8422144, 65536, 8586054, 9175586, 525062, 10486957, 9438443, 4195078,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint105AfterInverseMatrix *
    monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryVectorPoint105Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388612, 8388610, 8, 48, 32, 64, 8388800, 8389120, 8388864, 1024, 3697519, 8393472,
    8406752, 8398240, 8422144, 65536, 8586054, 9175586, 525062, 10486957, 9438443, 4195078,
    8388608]
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
    ![1041, 11007417, 512659, 11007854, 8388736, 58400, 8447088, 1072, 26608, 25104, 8388784,
    9132595, 13824, 8430496, 25696, 8976, 5352069, 11797829, 9671444, 16493831, 9495719,
    3155953, 6628280, 1200] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint55Transport monsterCo1GeometryVectorPoint57Transport 5
    monsterCo1GeometryVectorPoint55Matrix monsterCo1GeometryVectorPoint55InverseMatrix
    monsterCo1GeometryVectorPoint57Matrix
    monsterCo1GeometryVectorPoint105AfterSignMatrix
    monsterCo1GeometryVectorPoint105AfterInverseMatrix monsterCo1GeometryVectorPoint105Matrix
    monsterCo1GeometryVectorPoint55Transport_binary
    monsterCo1GeometryVectorPoint55Transport_inverse_binary
    monsterCo1GeometryVectorPoint57Transport_binary
    hc1 hc2 hc3 v

/-- Source point 105 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint105 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint105Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint105_binary :
    monsterCo1GeometryVectorPoint105.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint105Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint105Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
