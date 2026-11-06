/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixPacket10

/-! Complete actual matrix numerator covariance for all eleven lower source models. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every source model has all 576 exact ordered matrix covariance equations. -/
theorem generatedNinth_lower_spin_matrix_certificates :
    ∀ i j k, generatedNinthLowerSpinMatrixCondition i j k := by
  intro i j k
  fin_cases i
  · exact generatedNinth_lower_spin_matrix_packet_00 j k
  · exact generatedNinth_lower_spin_matrix_packet_01 j k
  · exact generatedNinth_lower_spin_matrix_packet_02 j k
  · exact generatedNinth_lower_spin_matrix_packet_03 j k
  · exact generatedNinth_lower_spin_matrix_packet_04 j k
  · exact generatedNinth_lower_spin_matrix_packet_05 j k
  · exact generatedNinth_lower_spin_matrix_packet_06 j k
  · exact generatedNinth_lower_spin_matrix_packet_07 j k
  · exact generatedNinth_lower_spin_matrix_packet_08 j k
  · exact generatedNinth_lower_spin_matrix_packet_09 j k
  · exact generatedNinth_lower_spin_matrix_packet_10 j k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
