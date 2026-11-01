/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartPacket05

/-! The complete original corrected mover starting boundary, retaining every signed coordinate. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original spin starting coordinate is the exact eightfold genuine pre-action on the source. -/
theorem generatedRootEight_mover_tensor_start_actual (j : Fin 24) (n : Fin 4096) :
    generatedRootEightMoverTensorSpinInteger 0 j n =
      8 * generatedRootEightMoverTensorPreInteger
        (fun m => generatedRootEightMoverTensorSourceInteger m j) n := by
  fin_cases j
  · exact generatedRootEight_mover_tensor_start_packet_00 0 n
  · exact generatedRootEight_mover_tensor_start_packet_00 1 n
  · exact generatedRootEight_mover_tensor_start_packet_00 2 n
  · exact generatedRootEight_mover_tensor_start_packet_00 3 n
  · exact generatedRootEight_mover_tensor_start_packet_01 0 n
  · exact generatedRootEight_mover_tensor_start_packet_01 1 n
  · exact generatedRootEight_mover_tensor_start_packet_01 2 n
  · exact generatedRootEight_mover_tensor_start_packet_01 3 n
  · exact generatedRootEight_mover_tensor_start_packet_02 0 n
  · exact generatedRootEight_mover_tensor_start_packet_02 1 n
  · exact generatedRootEight_mover_tensor_start_packet_02 2 n
  · exact generatedRootEight_mover_tensor_start_packet_02 3 n
  · exact generatedRootEight_mover_tensor_start_packet_03 0 n
  · exact generatedRootEight_mover_tensor_start_packet_03 1 n
  · exact generatedRootEight_mover_tensor_start_packet_03 2 n
  · exact generatedRootEight_mover_tensor_start_packet_03 3 n
  · exact generatedRootEight_mover_tensor_start_packet_04 0 n
  · exact generatedRootEight_mover_tensor_start_packet_04 1 n
  · exact generatedRootEight_mover_tensor_start_packet_04 2 n
  · exact generatedRootEight_mover_tensor_start_packet_04 3 n
  · exact generatedRootEight_mover_tensor_start_packet_05 0 n
  · exact generatedRootEight_mover_tensor_start_packet_05 1 n
  · exact generatedRootEight_mover_tensor_start_packet_05 2 n
  · exact generatedRootEight_mover_tensor_start_packet_05 3 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
