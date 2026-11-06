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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint045

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 93. -/
def monsterCo1GeometryVectorPoint93Transport : Co1 :=
  monsterCo1GeometryVectorPoint26Transport * monsterCo1GeometryTransportOperator 8 *
    monsterCo1GeometryVectorPoint26Transport⁻¹ * monsterCo1GeometryVectorPoint45Transport

/-- Complete displayed binary matrix of actual transport 93. -/
def monsterCo1GeometryVectorPoint93Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11191378, 2803008, 2282576, 2232652, 5392, 2753884, 53792, 2752768, 53248, 2753564,
      8438032, 8264608, 2765852, 4138672, 6990715, 6973943, 16221724, 1163296, 131340, 7813623,
      7700959, 7598069, 2763020, 272]

/-- First complete finite matrix product in literal actual transport 93. -/
def monsterCo1GeometryVectorPoint93AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 34144, 8405104, 53248, 8400912, 54064, 13264, 53520, 8401232, 8438032, 8931957,
      2802780, 12568526, 4720645, 4771097, 78262, 8704142, 144076, 578144, 8585401, 9175516,
      13126270, 8389632]

/-- Second complete finite matrix product in literal actual transport 93. -/
def monsterCo1GeometryVectorPoint93AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8390504, 8390260, 256, 8390430, 336, 946, 16, 8389950, 1296, 2279774, 4096,
      11150348, 10651426, 10634802, 16680904, 2670924, 8701744, 524560, 15680756, 704604,
      6472030, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 93 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint93Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint93Transport v =
      monsterCo1GeometryVectorPoint93Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint26Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 8422912, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 18443,
    2802780, 4179196, 4196363, 4246535, 78816, 315792, 144016, 578416, 197299, 786898, 4212736,
    8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint26InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 13993131, 5587115, 274, 323, 546, 643, 2, 3, 1036, 4212736, 8388876,
    8389388, 11, 8388615, 66531, 262546, 131731, 525170, 209584, 840144, 18443, 8389644] := by
      decide +kernel
  have hy : monsterCo1GeometryVectorPoint45Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11191378, 2803008, 10670636, 10670624, 53248, 8388944, 5936, 16, 5392, 8388624, 8389632,
    3596693, 2765852, 11154830, 10654242, 10655166, 8388730, 316338, 8570832, 7863527, 181369,
    6699383, 6476601, 272] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint93AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 34144, 8405104, 53248, 8400912, 54064, 13264, 53520, 8401232, 8438032, 8931957,
    2802780, 12568526, 4720645, 4771097, 78262, 8704142, 144076, 578144, 8585401, 9175516,
    13126270, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint93AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8390504, 8390260, 256, 8390430, 336, 946, 16, 8389950, 1296, 2279774, 4096,
    11150348, 10651426, 10634802, 16680904, 2670924, 8701744, 524560, 15680756, 704604,
    6472030, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint93Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11191378, 2803008, 2282576, 2232652, 5392, 2753884, 53792, 2752768, 53248, 2753564,
    8438032, 8264608, 2765852, 4138672, 6990715, 6973943, 16221724, 1163296, 131340, 7813623,
    7700959, 7598069, 2763020, 272] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint26Matrix *
    monsterCo1GeometryTransportOperatorMatrix 8 =
    monsterCo1GeometryVectorPoint93AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 8422912, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 18443,
    2802780, 4179196, 4196363, 4246535, 78816, 315792, 144016, 578416, 197299, 786898, 4212736,
    8389632]
      (monsterCo1GeometryBinaryOperatorMasks 8)
    ![768, 256, 34144, 8405104, 53248, 8400912, 54064, 13264, 53520, 8401232, 8438032, 8931957,
    2802780, 12568526, 4720645, 4771097, 78262, 8704142, 144076, 578144, 8585401, 9175516,
    13126270, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 8) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint93AfterSignMatrix *
    monsterCo1GeometryVectorPoint26InverseMatrix =
    monsterCo1GeometryVectorPoint93AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 34144, 8405104, 53248, 8400912, 54064, 13264, 53520, 8401232, 8438032, 8931957,
    2802780, 12568526, 4720645, 4771097, 78262, 8704142, 144076, 578144, 8585401, 9175516,
    13126270, 8389632]
    ![4129008, 2752592, 13993131, 5587115, 274, 323, 546, 643, 2, 3, 1036, 4212736, 8388876,
    8389388, 11, 8388615, 66531, 262546, 131731, 525170, 209584, 840144, 18443, 8389644]
    ![1, 2, 8390504, 8390260, 256, 8390430, 336, 946, 16, 8389950, 1296, 2279774, 4096,
    11150348, 10651426, 10634802, 16680904, 2670924, 8701744, 524560, 15680756, 704604,
    6472030, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint93AfterInverseMatrix *
    monsterCo1GeometryVectorPoint45Matrix = monsterCo1GeometryVectorPoint93Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8390504, 8390260, 256, 8390430, 336, 946, 16, 8389950, 1296, 2279774, 4096,
    11150348, 10651426, 10634802, 16680904, 2670924, 8701744, 524560, 15680756, 704604,
    6472030, 8388608]
    ![11191378, 2803008, 10670636, 10670624, 53248, 8388944, 5936, 16, 5392, 8388624, 8389632,
    3596693, 2765852, 11154830, 10654242, 10655166, 8388730, 316338, 8570832, 7863527, 181369,
    6699383, 6476601, 272]
    ![11191378, 2803008, 2282576, 2232652, 5392, 2753884, 53792, 2752768, 53248, 2753564,
    8438032, 8264608, 2765852, 4138672, 6990715, 6973943, 16221724, 1163296, 131340, 7813623,
    7700959, 7598069, 2763020, 272] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint26Transport monsterCo1GeometryVectorPoint45Transport 8
    monsterCo1GeometryVectorPoint26Matrix monsterCo1GeometryVectorPoint26InverseMatrix
    monsterCo1GeometryVectorPoint45Matrix
    monsterCo1GeometryVectorPoint93AfterSignMatrix
    monsterCo1GeometryVectorPoint93AfterInverseMatrix monsterCo1GeometryVectorPoint93Matrix
    monsterCo1GeometryVectorPoint26Transport_binary
    monsterCo1GeometryVectorPoint26Transport_inverse_binary
    monsterCo1GeometryVectorPoint45Transport_binary
    hc1 hc2 hc3 v

/-- Source point 93 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint93 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint93Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint93_binary :
    monsterCo1GeometryVectorPoint93.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint93Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint93Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
