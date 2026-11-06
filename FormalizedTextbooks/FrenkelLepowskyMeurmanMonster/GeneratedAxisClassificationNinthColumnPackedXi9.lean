/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9Packet15

/-! Original Gaussian transition from chronological column step 8 to 9. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_column_packed_xi_9_blocks (k : Fin 16) (m : Fin 256) :
    generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 8)
        ⟨256 * k.val + m.val, by omega⟩ =
      8 * generatedNinthColumnSpinPacked 9 ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_column_packed_xi_9_packet_00 m
  · exact generatedNinth_column_packed_xi_9_packet_01 m
  · exact generatedNinth_column_packed_xi_9_packet_02 m
  · exact generatedNinth_column_packed_xi_9_packet_03 m
  · exact generatedNinth_column_packed_xi_9_packet_04 m
  · exact generatedNinth_column_packed_xi_9_packet_05 m
  · exact generatedNinth_column_packed_xi_9_packet_06 m
  · exact generatedNinth_column_packed_xi_9_packet_07 m
  · exact generatedNinth_column_packed_xi_9_packet_08 m
  · exact generatedNinth_column_packed_xi_9_packet_09 m
  · exact generatedNinth_column_packed_xi_9_packet_10 m
  · exact generatedNinth_column_packed_xi_9_packet_11 m
  · exact generatedNinth_column_packed_xi_9_packet_12 m
  · exact generatedNinth_column_packed_xi_9_packet_13 m
  · exact generatedNinth_column_packed_xi_9_packet_14 m
  · exact generatedNinth_column_packed_xi_9_packet_15 m

/-- The original Gaussian agrees with the entire next cache and its exact clear factor. -/
theorem generatedNinth_column_packed_xi_step_9 (n : Fin 4096) :
    generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 8) n =
      8 * generatedNinthColumnSpinPacked 9 n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using generatedNinth_column_packed_xi_9_blocks k m

/-- This is the genuine original Gaussian with its exact integer clearing factor. -/
theorem generatedNinth_column_packed_xi_step_9_actual :
    nortonUIntegerXi (generatedNinthColumnSpinData 8) =
      fun n => 8 * generatedNinthColumnSpinData 9 n := by
  calc
    _ = generatedNinthColumnXiPacked (generatedNinthColumnSpinData 8) := by
      rw [generatedSixth_integer_xi_cached, generatedNinth_column_xi_packed]
    _ = generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 8) := by
      congr 1
      funext n
      exact (generatedNinth_column_spin_packed 8 n).symm
    _ = fun n => 8 * generatedNinthColumnSpinPacked 9 n := by
      funext n
      exact generatedNinth_column_packed_xi_step_9 n
    _ = fun n => 8 * generatedNinthColumnSpinData 9 n := by
      funext n
      rw [generatedNinth_column_spin_packed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
