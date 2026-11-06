/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitialPacket15

/-! Every original column-one input coordinate is bound to its genuine 64-state sum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_column_initial_blocks (k : Fin 16) (m : Fin 256) :
    generatedNinthColumnSpinData 0 ⟨256 * k.val + m.val, by omega⟩ =
      generatedNinthColumnInputSparse 1 ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_column_initial_packet_00 m
  · exact generatedNinth_column_initial_packet_01 m
  · exact generatedNinth_column_initial_packet_02 m
  · exact generatedNinth_column_initial_packet_03 m
  · exact generatedNinth_column_initial_packet_04 m
  · exact generatedNinth_column_initial_packet_05 m
  · exact generatedNinth_column_initial_packet_06 m
  · exact generatedNinth_column_initial_packet_07 m
  · exact generatedNinth_column_initial_packet_08 m
  · exact generatedNinth_column_initial_packet_09 m
  · exact generatedNinth_column_initial_packet_10 m
  · exact generatedNinth_column_initial_packet_11 m
  · exact generatedNinth_column_initial_packet_12 m
  · exact generatedNinth_column_initial_packet_13 m
  · exact generatedNinth_column_initial_packet_14 m
  · exact generatedNinth_column_initial_packet_15 m

/-- The displayed initial cache is the exact original column-one input at every spin label. -/
theorem generatedNinth_column_initial_certificate (n : Fin 4096) :
    generatedNinthColumnSpinData 0 n = generatedNinthColumnInputSparse 1 n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using generatedNinth_column_initial_blocks k m

/-- The cache is the complete actual input vector, with no support assumption. -/
theorem generatedNinth_column_initial_actual :
    generatedNinthColumnSpinData 0 = generatedNinthColumnInputInteger 1 := by
  funext n
  rw [generatedNinth_column_initial_certificate, generatedNinth_column_input_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
