/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7Packet15

/-! The step 7 original signed permutation transition uses the proved packed decoder. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_column_packed_permutation_7_blocks
    (k : Fin 16) (m : Fin 256) :
    generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 6)
        ⟨256 * k.val + m.val, by omega⟩ =
      generatedNinthColumnSpinPacked 7 ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_column_packed_permutation_7_packet_00 m
  · exact generatedNinth_column_packed_permutation_7_packet_01 m
  · exact generatedNinth_column_packed_permutation_7_packet_02 m
  · exact generatedNinth_column_packed_permutation_7_packet_03 m
  · exact generatedNinth_column_packed_permutation_7_packet_04 m
  · exact generatedNinth_column_packed_permutation_7_packet_05 m
  · exact generatedNinth_column_packed_permutation_7_packet_06 m
  · exact generatedNinth_column_packed_permutation_7_packet_07 m
  · exact generatedNinth_column_packed_permutation_7_packet_08 m
  · exact generatedNinth_column_packed_permutation_7_packet_09 m
  · exact generatedNinth_column_packed_permutation_7_packet_10 m
  · exact generatedNinth_column_packed_permutation_7_packet_11 m
  · exact generatedNinth_column_packed_permutation_7_packet_12 m
  · exact generatedNinth_column_packed_permutation_7_packet_13 m
  · exact generatedNinth_column_packed_permutation_7_packet_14 m
  · exact generatedNinth_column_packed_permutation_7_packet_15 m

/-- Every original coordinate follows the exact signed permutation operator. -/
theorem generatedNinth_column_packed_permutation_7 (n : Fin 4096) :
    generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 6) n =
      generatedNinthColumnSpinPacked 7 n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using generatedNinth_column_packed_permutation_7_blocks k m

/-- The whole step 7 cache transition is the genuine original spin permutation. -/
theorem generatedNinth_column_packed_permutation_7_actual :
    generatedNinthIntegerPermutation 1 (generatedNinthColumnSpinData 6) =
      generatedNinthColumnSpinData 7 := by
  calc
    _ = generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 6) := by
      rw [generatedNinth_column_permutation_fast]
      congr 1
      funext n
      exact (generatedNinth_column_spin_packed 6 n).symm
    _ = generatedNinthColumnSpinPacked 7 := by
      funext n
      exact generatedNinth_column_packed_permutation_7 n
    _ = generatedNinthColumnSpinData 7 := by
      funext n
      exact generatedNinth_column_spin_packed 7 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
