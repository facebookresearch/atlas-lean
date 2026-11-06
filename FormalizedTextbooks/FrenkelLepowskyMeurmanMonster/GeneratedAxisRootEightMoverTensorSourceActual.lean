/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourcePacket05

/-! Every original mover source coordinate is bound to the full actual raw tensor cache. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every raw source coordinate has its actual original value, including signs and zeros. -/
theorem generatedRootEight_mover_tensor_source_actual (n : Fin 4096) (j : Fin 24) :
    generatedRootEightMoverTensorSourceInteger n j = generatedRootEightCanonicalTensorRawCache n j := by
  fin_cases j
  · exact generatedRootEight_mover_tensor_source_packet_00 0 n
  · exact generatedRootEight_mover_tensor_source_packet_00 1 n
  · exact generatedRootEight_mover_tensor_source_packet_00 2 n
  · exact generatedRootEight_mover_tensor_source_packet_00 3 n
  · exact generatedRootEight_mover_tensor_source_packet_01 0 n
  · exact generatedRootEight_mover_tensor_source_packet_01 1 n
  · exact generatedRootEight_mover_tensor_source_packet_01 2 n
  · exact generatedRootEight_mover_tensor_source_packet_01 3 n
  · exact generatedRootEight_mover_tensor_source_packet_02 0 n
  · exact generatedRootEight_mover_tensor_source_packet_02 1 n
  · exact generatedRootEight_mover_tensor_source_packet_02 2 n
  · exact generatedRootEight_mover_tensor_source_packet_02 3 n
  · exact generatedRootEight_mover_tensor_source_packet_03 0 n
  · exact generatedRootEight_mover_tensor_source_packet_03 1 n
  · exact generatedRootEight_mover_tensor_source_packet_03 2 n
  · exact generatedRootEight_mover_tensor_source_packet_03 3 n
  · exact generatedRootEight_mover_tensor_source_packet_04 0 n
  · exact generatedRootEight_mover_tensor_source_packet_04 1 n
  · exact generatedRootEight_mover_tensor_source_packet_04 2 n
  · exact generatedRootEight_mover_tensor_source_packet_04 3 n
  · exact generatedRootEight_mover_tensor_source_packet_05 0 n
  · exact generatedRootEight_mover_tensor_source_packet_05 1 n
  · exact generatedRootEight_mover_tensor_source_packet_05 2 n
  · exact generatedRootEight_mover_tensor_source_packet_05 3 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
