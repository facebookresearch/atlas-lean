/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryPacket11

/-! All complete actual candidate lattice actions match the source binary columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every whole candidate lattice basis column retains its actual compact binary image. -/
theorem generatedTwelfth_certified_matrix_binary_columns (g : Fin 12) (j : Fin 24) :
    (leechHyperbolicInverse *
      (generatedTwelfthCertifiedIntegral g).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j) := by
  fin_cases g
  · exact generatedTwelfth_certified_matrix_binary_packet_00 j
  · exact generatedTwelfth_certified_matrix_binary_packet_01 j
  · exact generatedTwelfth_certified_matrix_binary_packet_02 j
  · exact generatedTwelfth_certified_matrix_binary_packet_03 j
  · exact generatedTwelfth_certified_matrix_binary_packet_04 j
  · exact generatedTwelfth_certified_matrix_binary_packet_05 j
  · exact generatedTwelfth_certified_matrix_binary_packet_06 j
  · exact generatedTwelfth_certified_matrix_binary_packet_07 j
  · exact generatedTwelfth_certified_matrix_binary_packet_08 j
  · exact generatedTwelfth_certified_matrix_binary_packet_09 j
  · exact generatedTwelfth_certified_matrix_binary_packet_10 j
  · exact generatedTwelfth_certified_matrix_binary_packet_11 j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
