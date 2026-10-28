/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8Packet15

/-! Original Gaussian transition from chronological column step 7 to 8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_column_packed_xi_8_blocks (k : Fin 16) (m : Fin 256) :
    generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 7)
        ⟨256 * k.val + m.val, by omega⟩ =
      16 * generatedNinthColumnSpinPacked 8 ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_column_packed_xi_8_packet_00 m
  · exact generatedNinth_column_packed_xi_8_packet_01 m
  · exact generatedNinth_column_packed_xi_8_packet_02 m
  · exact generatedNinth_column_packed_xi_8_packet_03 m
  · exact generatedNinth_column_packed_xi_8_packet_04 m
  · exact generatedNinth_column_packed_xi_8_packet_05 m
  · exact generatedNinth_column_packed_xi_8_packet_06 m
  · exact generatedNinth_column_packed_xi_8_packet_07 m
  · exact generatedNinth_column_packed_xi_8_packet_08 m
  · exact generatedNinth_column_packed_xi_8_packet_09 m
  · exact generatedNinth_column_packed_xi_8_packet_10 m
  · exact generatedNinth_column_packed_xi_8_packet_11 m
  · exact generatedNinth_column_packed_xi_8_packet_12 m
  · exact generatedNinth_column_packed_xi_8_packet_13 m
  · exact generatedNinth_column_packed_xi_8_packet_14 m
  · exact generatedNinth_column_packed_xi_8_packet_15 m

/-- The original Gaussian agrees with the entire next cache and its exact clear factor. -/
theorem generatedNinth_column_packed_xi_step_8 (n : Fin 4096) :
    generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 7) n =
      16 * generatedNinthColumnSpinPacked 8 n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using generatedNinth_column_packed_xi_8_blocks k m

/-- This is the genuine original Gaussian with its exact integer clearing factor. -/
theorem generatedNinth_column_packed_xi_step_8_actual :
    nortonUIntegerXi (generatedNinthColumnSpinData 7) =
      fun n => 16 * generatedNinthColumnSpinData 8 n := by
  calc
    _ = generatedNinthColumnXiPacked (generatedNinthColumnSpinData 7) := by
      rw [generatedSixth_integer_xi_cached, generatedNinth_column_xi_packed]
    _ = generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 7) := by
      congr 1
      funext n
      exact (generatedNinth_column_spin_packed 7 n).symm
    _ = fun n => 16 * generatedNinthColumnSpinPacked 8 n := by
      funext n
      exact generatedNinth_column_packed_xi_step_8 n
    _ = fun n => 16 * generatedNinthColumnSpinData 8 n := by
      funext n
      rw [generatedNinth_column_spin_packed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
