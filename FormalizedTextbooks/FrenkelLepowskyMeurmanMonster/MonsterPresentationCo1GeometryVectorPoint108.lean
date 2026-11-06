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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint058
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint060

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 108. -/
def monsterCo1GeometryVectorPoint108Transport : Co1 :=
  monsterCo1GeometryVectorPoint58Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint58Transport⁻¹ * monsterCo1GeometryVectorPoint60Transport

/-- Complete displayed binary matrix of actual transport 108. -/
def monsterCo1GeometryVectorPoint108Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 2371211, 8711360, 9751264, 1152, 1073, 1056, 8447072, 8398589, 9479030, 1184,
      3448863, 3260034, 9496189, 10526768, 3188413, 5451840, 11850879, 5875787, 3215603,
      10502267, 1048576, 6964230, 58497]

/-- First complete finite matrix product in literal actual transport 108. -/
def monsterCo1GeometryVectorPoint108AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57488, 29824, 29664, 53712, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104, 58368,
      12910626, 13637695, 1090561, 2121824, 3194960, 4406356, 9574102, 5799621, 16531256, 1771,
      11543846, 14076151, 8389632]

/-- Second complete finite matrix product in literal actual transport 108. -/
def monsterCo1GeometryVectorPoint108AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 4, 8, 16, 8388640, 8388672, 8388736, 8388864, 8389120, 8389632, 8265376,
      4894, 9821, 18155, 33895, 65891, 8520348, 262942, 8913188, 1049809, 10486887, 12583694,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 108 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint108Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint108Transport v =
      monsterCo1GeometryVectorPoint108Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint58Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447120, 29824, 29664, 53712, 8389648, 58416, 58560, 58432, 34000, 17520, 8445952,
    12910604, 5245503, 9479681, 2122080, 3195728, 12789860, 9573574, 14183621, 8136760,
    8390379, 3154470, 5692135, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint58InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58400, 5141206, 7271500, 6198282, 8388624, 1072, 8389760, 192, 1771, 652, 8389841,
    12654962, 1347, 1825, 8390257, 8388993, 3379337, 2246549, 3982716, 1373536, 49164, 18187,
    4143458, 1233] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint60Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 2371211, 8711360, 9751264, 1152, 57520, 57505, 8388833, 8438396, 9455607, 57377,
    1257888, 1390370, 9470971, 8446764, 1082519, 7855351, 11818312, 8200683, 3488382, 10503371,
    3196587, 5123495, 58497] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint108AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57488, 29824, 29664, 53712, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104, 58368,
    12910626, 13637695, 1090561, 2121824, 3194960, 4406356, 9574102, 5799621, 16531256, 1771,
    11543846, 14076151, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint108AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 4, 8, 16, 8388640, 8388672, 8388736, 8388864, 8389120, 8389632, 8265376,
    4894, 9821, 18155, 33895, 65891, 8520348, 262942, 8913188, 1049809, 10486887, 12583694,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint108Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 2371211, 8711360, 9751264, 1152, 1073, 1056, 8447072, 8398589, 9479030, 1184,
    3448863, 3260034, 9496189, 10526768, 3188413, 5451840, 11850879, 5875787, 3215603,
    10502267, 1048576, 6964230, 58497] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint58Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint108AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447120, 29824, 29664, 53712, 8389648, 58416, 58560, 58432, 34000, 17520, 8445952,
    12910604, 5245503, 9479681, 2122080, 3195728, 12789860, 9573574, 14183621, 8136760,
    8390379, 3154470, 5692135, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![57488, 29824, 29664, 53712, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104, 58368,
    12910626, 13637695, 1090561, 2121824, 3194960, 4406356, 9574102, 5799621, 16531256, 1771,
    11543846, 14076151, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint108AfterSignMatrix *
    monsterCo1GeometryVectorPoint58InverseMatrix =
    monsterCo1GeometryVectorPoint108AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57488, 29824, 29664, 53712, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104, 58368,
    12910626, 13637695, 1090561, 2121824, 3194960, 4406356, 9574102, 5799621, 16531256, 1771,
    11543846, 14076151, 8389632]
    ![58400, 5141206, 7271500, 6198282, 8388624, 1072, 8389760, 192, 1771, 652, 8389841,
    12654962, 1347, 1825, 8390257, 8388993, 3379337, 2246549, 3982716, 1373536, 49164, 18187,
    4143458, 1233]
    ![8388609, 2, 4, 8, 16, 8388640, 8388672, 8388736, 8388864, 8389120, 8389632, 8265376,
    4894, 9821, 18155, 33895, 65891, 8520348, 262942, 8913188, 1049809, 10486887, 12583694,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint108AfterInverseMatrix *
    monsterCo1GeometryVectorPoint60Matrix = monsterCo1GeometryVectorPoint108Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 2, 4, 8, 16, 8388640, 8388672, 8388736, 8388864, 8389120, 8389632, 8265376,
    4894, 9821, 18155, 33895, 65891, 8520348, 262942, 8913188, 1049809, 10486887, 12583694,
    8388608]
    ![8388689, 2371211, 8711360, 9751264, 1152, 57520, 57505, 8388833, 8438396, 9455607, 57377,
    1257888, 1390370, 9470971, 8446764, 1082519, 7855351, 11818312, 8200683, 3488382, 10503371,
    3196587, 5123495, 58497]
    ![8447184, 2371211, 8711360, 9751264, 1152, 1073, 1056, 8447072, 8398589, 9479030, 1184,
    3448863, 3260034, 9496189, 10526768, 3188413, 5451840, 11850879, 5875787, 3215603,
    10502267, 1048576, 6964230, 58497] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint58Transport monsterCo1GeometryVectorPoint60Transport 1
    monsterCo1GeometryVectorPoint58Matrix monsterCo1GeometryVectorPoint58InverseMatrix
    monsterCo1GeometryVectorPoint60Matrix
    monsterCo1GeometryVectorPoint108AfterSignMatrix
    monsterCo1GeometryVectorPoint108AfterInverseMatrix monsterCo1GeometryVectorPoint108Matrix
    monsterCo1GeometryVectorPoint58Transport_binary
    monsterCo1GeometryVectorPoint58Transport_inverse_binary
    monsterCo1GeometryVectorPoint60Transport_binary
    hc1 hc2 hc3 v

/-- Source point 108 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint108 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint108Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint108_binary :
    monsterCo1GeometryVectorPoint108.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint108Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint108Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
