/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishPacket05

/-! Exact original mover tensor boundaries and positive spatial coefficients. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The actual monomial post action agrees with every original final coordinate, including zeros. -/
theorem generatedRootEight_mover_tensor_finish_actual (j : Fin 24) (n : Fin 4096) :
    generatedRootEightMoverTensorPostInteger (generatedRootEightMoverTensorSpinInteger 3 j) n =
      generatedRootEightMoverTensorFinalInteger n j := by
  fin_cases j
  · exact generatedRootEight_mover_tensor_finish_packet_00 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_00 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_00 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_00 3 n
  · exact generatedRootEight_mover_tensor_finish_packet_01 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_01 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_01 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_01 3 n
  · exact generatedRootEight_mover_tensor_finish_packet_02 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_02 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_02 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_02 3 n
  · exact generatedRootEight_mover_tensor_finish_packet_03 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_03 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_03 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_03 3 n
  · exact generatedRootEight_mover_tensor_finish_packet_04 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_04 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_04 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_04 3 n
  · exact generatedRootEight_mover_tensor_finish_packet_05 0 n
  · exact generatedRootEight_mover_tensor_finish_packet_05 1 n
  · exact generatedRootEight_mover_tensor_finish_packet_05 2 n
  · exact generatedRootEight_mover_tensor_finish_packet_05 3 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
